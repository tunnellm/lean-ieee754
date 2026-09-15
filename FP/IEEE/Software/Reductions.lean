import FP.IEEE.Software.ScaledRound
import FP.IEEE.Summation
import FP.IEEE.MixedDot
import FP.Range.Checker

/-! Executable nearest-even reductions and refinement to the IEEE finite-value
specification. These proofs do not import or assume a native Float model bridge.
`none` propagates overflow. These are rational-value results, not yet total IEEE
result encodings or exception traces. -/
namespace FP.IEEE.Software
open scoped BigOperators

private def addResults (F : Format) (a b : Option ℚ) : Option ℚ := do
  let x ← a
  let y ← b
  roundNearest? F (x + y)

def sumTree? (F : Format) (a : ℕ → ℚ) : ReductionTree → Option ℚ
  | .zero => some 0
  | .input i => some (a i)
  | .add l r => addResults F (sumTree? F a l) (sumTree? F a r)

def sequentialSum? (F : Format) (a : ℕ → ℚ) (n : ℕ) : Option ℚ :=
  sumTree? F a (sequentialTree 0 n)

def pairwiseSum? (F : Format) (a : ℕ → ℚ) (n : ℕ) : Option ℚ :=
  sumTree? F a (pairwiseTree 0 n)

/-- Zero-started sequential dot product, with separate multiplication and addition. -/
def dot? (F : Format) (a b : ℕ → ℚ) : ℕ → Option ℚ
  | 0 => some 0
  | n + 1 => addResults F (dot? F a b n) (roundNearest? F (a n * b n))

private theorem addResults_cast (F : Format) (a b : Option ℚ) :
    (addResults F a b).map (fun q : ℚ => (q : ℝ)) =
      (do let x ← a.map (fun q : ℚ => (q : ℝ))
          let y ← b.map (fun q : ℚ => (q : ℝ))
          F.round? (x + y)) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      change (roundNearest? F (a + b)).map (fun q : ℚ => (q : ℝ)) = F.round? ((a : ℝ) + b)
      simpa only [Rat.cast_add] using roundNearest?_cast F (a + b)

/-- Refinement includes overflow: neither side needs a nonoverflow hypothesis. -/
theorem sumTree?_cast (F : Format) (a : ℕ → ℚ) (t : ReductionTree) :
    (sumTree? F a t).map (fun q : ℚ => (q : ℝ)) = F.sumTree? (fun i => (a i : ℝ)) t := by
  induction t with
  | zero => simp [sumTree?, Format.sumTree?]
  | input i => rfl
  | add l r hl hr =>
    simp only [sumTree?, addResults_cast, hl, hr, Format.sumTree?]

theorem sequentialSum?_cast (F : Format) (a : ℕ → ℚ) (n : ℕ) :
    (sequentialSum? F a n).map (fun q : ℚ => (q : ℝ)) =
      F.sequentialSum? (fun i => (a i : ℝ)) n := sumTree?_cast F a _

theorem pairwiseSum?_cast (F : Format) (a : ℕ → ℚ) (n : ℕ) :
    (pairwiseSum? F a n).map (fun q : ℚ => (q : ℝ)) =
      F.pairwiseSum? (fun i => (a i : ℝ)) n := sumTree?_cast F a _

theorem dot?_cast (F : Format) (a b : ℕ → ℚ) (n : ℕ) :
    (dot? F a b n).map (fun q : ℚ => (q : ℝ)) =
      F.dot? (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) n := by
  induction n with
  | zero => simp [dot?, Format.dot?]
  | succ n ih =>
    simp only [dot?, addResults_cast, ih, roundNearest?_cast, Rat.cast_mul, Format.dot?]

/-- A successful range certificate proves a finite software result, its enclosure,
and the mixed error bound. No native equivalence hypothesis is used. -/
theorem sumTree?_mixed_of_certificate (F : Format) (a : ℕ → ℚ)
    (bounds : ℕ → FP.Range.Interval) (t : ReductionTree)
    (hb : ∀ i ∈ t.leaves, (bounds i).Contains (a i : ℝ))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat F) bounds t = some enclosure) :
    ∃ q : ℚ, sumTree? F a t = some q ∧ enclosure.Contains (q : ℝ) ∧
      |(q : ℝ) - t.exactSum (fun i => (a i : ℝ))| ≤
        growth F.unitRoundoff t.height * t.mass (fun i => (a i : ℝ)) +
          (F.minSubnormal / 2) * t.roundWeight F.unitRoundoff := by
  obtain ⟨ht, he⟩ := FP.Range.checkSum_sound F bounds (fun i => (a i : ℝ)) t hb hc
  have hv := (sumTree?_cast F a t).trans (F.sumTree?_eq_of_nonoverflow _ t ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨q, hq, hval ▸ he, hval ▸ F.sumTree_mixed_error (fun i => (a i : ℝ)) t⟩

theorem sequentialSum?_mixed_of_certificate (F : Format) (a : ℕ → ℚ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hb : ∀ i < n, (bounds i).Contains (a i : ℝ))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat F) bounds (sequentialTree 0 n) = some enclosure) :
    ∃ q : ℚ, sequentialSum? F a n = some q ∧ enclosure.Contains (q : ℝ) ∧
      |(q : ℝ) - ∑ i ∈ Finset.range n, (a i : ℝ)| ≤
        growth F.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |(a i : ℝ)|) +
          (F.minSubnormal / 2) * geomWeight F.unitRoundoff (n - 1) := by
  simpa only [sequentialSum?, sequentialTree_exactSum, ReductionTree.mass,
    sequentialTree_height, sequentialTree_roundWeight] using
    sumTree?_mixed_of_certificate F a bounds (sequentialTree 0 n)
      (fun i hi => hb i (by simpa using hi)) hc

theorem pairwiseSum?_mixed_of_certificate (F : Format) (a : ℕ → ℚ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hb : ∀ i < n, (bounds i).Contains (a i : ℝ))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat F) bounds (pairwiseTree 0 n) = some enclosure) :
    ∃ q : ℚ, pairwiseSum? F a n = some q ∧ enclosure.Contains (q : ℝ) ∧
      |(q : ℝ) - ∑ i ∈ Finset.range n, (a i : ℝ)| ≤
        growth F.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |(a i : ℝ)|) +
          (F.minSubnormal / 2) * (pairwiseTree 0 n).roundWeight F.unitRoundoff := by
  simpa only [pairwiseSum?, pairwiseTree_exactSum, ReductionTree.mass, pairwiseTree_height] using
    sumTree?_mixed_of_certificate F a bounds (pairwiseTree 0 n)
      (fun i hi => hb i (by simpa using hi)) hc

theorem dot?_mixed_of_certificate (F : Format) (a b : ℕ → ℚ)
    (ba bb : ℕ → FP.Range.Interval) (n : ℕ)
    (ha : ∀ i < n, (ba i).Contains (a i : ℝ))
    (hb : ∀ i < n, (bb i).Contains (b i : ℝ))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkDot (.ofFormat F) ba bb n = some enclosure) :
    ∃ q : ℚ, dot? F a b n = some q ∧ enclosure.Contains (q : ℝ) ∧
      MixedBackwardStable (growth F.unitRoundoff (2 * n))
        (dotResidual F.unitRoundoff (F.minSubnormal / 2) n)
        (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) n (q : ℝ) := by
  obtain ⟨ht, he⟩ := FP.Range.checkDot_sound F ba bb _ _ n ha hb hc
  have hv := (dot?_cast F a b n).trans (F.dot?_eq_of_nonoverflow _ _ n ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  have herr := FP.roundedDot_mixed_backward F.unitRoundoff_pos.le
    (show 0 ≤ F.minSubnormal / 2 by unfold Format.minSubnormal; positivity)
    F.roundFinite _ (fun z _ => F.roundFinite_mixed_error z) _ _ n ht
  exact ⟨q, hq, hval ▸ he, hval ▸ herr⟩

theorem dot?_mixed_gamma_of_certificate (F : Format) (a b : ℕ → ℚ)
    (ba bb : ℕ → FP.Range.Interval) (n : ℕ)
    (ha : ∀ i < n, (ba i).Contains (a i : ℝ))
    (hb : ∀ i < n, (bb i).Contains (b i : ℝ))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkDot (.ofFormat F) ba bb n = some enclosure)
    (hn : (2 * n : ℕ) * F.unitRoundoff < 1) :
    ∃ q : ℚ, dot? F a b n = some q ∧ enclosure.Contains (q : ℝ) ∧
      MixedBackwardStable (gamma F.unitRoundoff (2 * n))
        (dotResidual F.unitRoundoff (F.minSubnormal / 2) n)
        (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) n (q : ℝ) := by
  obtain ⟨q, hq, he, hback⟩ := dot?_mixed_of_certificate F a b ba bb n ha hb hc
  exact ⟨q, hq, he, hback.mono (growth_le_gamma F.unitRoundoff_pos.le _ hn) le_rfl⟩

/-- The traditional purely relative bound remains available under its stronger
normal-range qualifications. Underflow is covered instead by the mixed theorem. -/
theorem dot?_backward (F : Format) (a b : ℕ → ℚ) (n : ℕ)
    (hs : F.SafeDot (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) n)
    (hn : (2 * n : ℕ) * F.unitRoundoff < 1) :
    ∃ q : ℚ, dot? F a b n = some q ∧
      BackwardStable (gamma F.unitRoundoff (2 * n))
        (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) n (q : ℝ) := by
  obtain ⟨s, hs, hb⟩ := F.innerProduct_backward _ _ n hs hn
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp ((dot?_cast F a b n).trans hs)
  exact ⟨q, hq, hval ▸ hb⟩

/-- Raw-word summation: decode only leaves actually used by the schedule. -/
def wordSumTree? (I : Interchange) (a : ℕ → I.Word) : ReductionTree → Option ℚ
  | .zero => some 0
  | .input i => (Interchange.Datum.decode I (a i)).toRat?
  | .add l r => addResults I.format (wordSumTree? I a l) (wordSumTree? I a r)

def wordSequentialSum? (I : Interchange) (a : ℕ → I.Word) (n : ℕ) : Option ℚ :=
  wordSumTree? I a (sequentialTree 0 n)

def wordPairwiseSum? (I : Interchange) (a : ℕ → I.Word) (n : ℕ) : Option ℚ :=
  wordSumTree? I a (pairwiseTree 0 n)

private def mulResults (F : Format) (a b : Option ℚ) : Option ℚ := do
  let x ← a
  let y ← b
  roundNearest? F (x * y)

private theorem mulResults_cast (F : Format) (a b : Option ℚ) :
    (mulResults F a b).map (fun q : ℚ => (q : ℝ)) =
      (do let x ← a.map (fun q : ℚ => (q : ℝ))
          let y ← b.map (fun q : ℚ => (q : ℝ))
          F.round? (x * y)) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      change (roundNearest? F (a * b)).map (fun q : ℚ => (q : ℝ)) = F.round? ((a : ℝ) * b)
      simpa only [Rat.cast_mul] using roundNearest?_cast F (a * b)

/-- Raw-word dot product; no input conversion error is added to decoded finite operands. -/
def wordDot? (I : Interchange) (a b : ℕ → I.Word) : ℕ → Option ℚ
  | 0 => some 0
  | n + 1 => addResults I.format (wordDot? I a b n)
      (mulResults I.format (Interchange.Datum.decode I (a n)).toRat?
        (Interchange.Datum.decode I (b n)).toRat?)

theorem wordSumTree?_cast (I : Interchange) [I.Valid] (a : ℕ → I.Word) (x : ℕ → ℝ)
    (t : ReductionTree) (hx : ∀ i ∈ t.leaves, I.decode? (a i) = some (x i)) :
    (wordSumTree? I a t).map (fun q : ℚ => (q : ℝ)) = I.format.sumTree? x t := by
  induction t with
  | zero => simp [wordSumTree?, Format.sumTree?]
  | input i =>
    exact (Interchange.Datum.toRat?_decode I (a i)).trans (hx i (by simp [ReductionTree.leaves]))
  | add l r hl hr =>
    have hL := hl (fun i hi => hx i (by simp [ReductionTree.leaves, hi]))
    have hR := hr (fun i hi => hx i (by simp [ReductionTree.leaves, hi]))
    simp only [wordSumTree?, addResults_cast, hL, hR, Format.sumTree?]

theorem wordDot?_cast (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ)
    (n : ℕ) (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hy : ∀ i < n, I.decode? (b i) = some (y i)) :
    (wordDot? I a b n).map (fun q : ℚ => (q : ℝ)) = I.format.dot? x y n := by
  induction n with
  | zero => simp [wordDot?, Format.dot?]
  | succ n ih =>
    have hn := ih (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    simp only [wordDot?, addResults_cast, mulResults_cast, hn,
      Interchange.Datum.toRat?_decode, hx n (by omega), hy n (by omega), Format.dot?]
    rfl

/-- Complementary summation guarantee for actual interchange input encodings. -/
theorem wordSumTree?_mixed_of_certificate (I : Interchange) [I.Valid]
    (a : ℕ → I.Word) (x : ℕ → ℝ) (bounds : ℕ → FP.Range.Interval) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, I.decode? (a i) = some (x i))
    (hb : ∀ i ∈ t.leaves, (bounds i).Contains (x i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat I.format) bounds t = some enclosure) :
    ∃ q : ℚ, wordSumTree? I a t = some q ∧ enclosure.Contains (q : ℝ) ∧
      |(q : ℝ) - t.exactSum x| ≤
        growth I.format.unitRoundoff t.height * t.mass x +
          (I.format.minSubnormal / 2) * t.roundWeight I.format.unitRoundoff := by
  obtain ⟨ht, he⟩ := FP.Range.checkSum_sound I.format bounds x t hb hc
  have hv := (wordSumTree?_cast I a x t hx).trans (I.format.sumTree?_eq_of_nonoverflow x t ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨q, hq, hval ▸ he, hval ▸ I.format.sumTree_mixed_error x t⟩

/-- Complementary mixed backward guarantee for raw-word dot products, including underflow. -/
theorem wordDot?_mixed_of_certificate (I : Interchange) [I.Valid]
    (a b : ℕ → I.Word) (x y : ℕ → ℝ) (ba bb : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hy : ∀ i < n, I.decode? (b i) = some (y i))
    (ha : ∀ i < n, (ba i).Contains (x i))
    (hb : ∀ i < n, (bb i).Contains (y i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkDot (.ofFormat I.format) ba bb n = some enclosure) :
    ∃ q : ℚ, wordDot? I a b n = some q ∧ enclosure.Contains (q : ℝ) ∧
      MixedBackwardStable (growth I.format.unitRoundoff (2 * n))
        (dotResidual I.format.unitRoundoff (I.format.minSubnormal / 2) n) x y n (q : ℝ) := by
  obtain ⟨ht, he⟩ := FP.Range.checkDot_sound I.format ba bb x y n ha hb hc
  have hv := (wordDot?_cast I a b x y n hx hy).trans (I.format.dot?_eq_of_nonoverflow x y n ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  have herr := FP.roundedDot_mixed_backward I.format.unitRoundoff_pos.le
    (show 0 ≤ I.format.minSubnormal / 2 by unfold Format.minSubnormal; positivity)
    I.format.roundFinite _ (fun z _ => I.format.roundFinite_mixed_error z) x y n ht
  exact ⟨q, hq, hval ▸ he, hval ▸ herr⟩

private theorem trace_nonoverflow_of_safe (F : Format) (x : ℕ → ℝ) (t : ReductionTree)
    (hs : t.Trace F.Safe F.roundFinite x) :
    t.Trace (fun z => |z| < F.overflowThreshold) F.roundFinite x := by
  induction t with
  | zero => trivial
  | input i => trivial
  | add l r hl hr =>
    refine ⟨hl hs.1, hr hs.2.1, ?_⟩
    rcases hs.2.2 with hz | hn
    · rw [hz, abs_zero]; exact F.overflowThreshold_pos
    · exact hn.2

theorem sequentialSum?_backward (F : Format) (a : ℕ → ℚ) (n : ℕ)
    (hs : (sequentialTree 0 n).Trace F.Safe F.roundFinite (fun i => (a i : ℝ)))
    (hn : ((n - 1 : ℕ) : ℝ) * F.unitRoundoff < 1) :
    ∃ q : ℚ, sequentialSum? F a n = some q ∧
      BackwardStable (gamma F.unitRoundoff (n - 1))
        (fun i => (a i : ℝ)) (fun _ => 1) n (q : ℝ) := by
  have ht := trace_nonoverflow_of_safe F _ _ hs
  have hv := (sequentialSum?_cast F a n).trans (F.sumTree?_eq_of_nonoverflow _ _ ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  have he := FP.sequentialSum_backward_gamma F.unitRoundoff_pos.le F.roundFinite F.Safe
    (fun _ hz => F.roundFinite_relativeError hz) (fun i => (a i : ℝ)) n hs hn
  exact ⟨q, hq, hval ▸ he⟩

theorem pairwiseSum?_backward (F : Format) (a : ℕ → ℚ) (n : ℕ)
    (hs : (pairwiseTree 0 n).Trace F.Safe F.roundFinite (fun i => (a i : ℝ)))
    (hn : ((Nat.clog 2 n : ℕ) : ℝ) * F.unitRoundoff < 1) :
    ∃ q : ℚ, pairwiseSum? F a n = some q ∧
      BackwardStable (gamma F.unitRoundoff (Nat.clog 2 n))
        (fun i => (a i : ℝ)) (fun _ => 1) n (q : ℝ) := by
  have ht := trace_nonoverflow_of_safe F _ _ hs
  have hv := (pairwiseSum?_cast F a n).trans (F.sumTree?_eq_of_nonoverflow _ _ ht)
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  have he := FP.pairwiseSum_backward_gamma F.unitRoundoff_pos.le F.roundFinite F.Safe
    (fun _ hz => F.roundFinite_relativeError hz) (fun i => (a i : ℝ)) n hs hn
  exact ⟨q, hq, hval ▸ he⟩

end FP.IEEE.Software
