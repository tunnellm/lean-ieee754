import FP.IEEE.Software.TotalReductions

/-! Numerical theorems for total word-valued reductions. Range certificates
permit gradual underflow; pure relative backward results retain Safe traces. -/
namespace FP.IEEE.Software
open Interchange
open scoped BigOperators

private theorem decode_of_rat (I : Interchange) [I.Valid] (w : I.Word) (q : ℚ)
    (h : (Datum.decode I w).toRat? = some q) : I.decode? w = some (q : ℝ) := by
  rw [← Datum.toRat?_decode, h]
  rfl

theorem sumTree_mixed_of_certificate (I : Interchange) [I.Valid]
    (a : ℕ → I.Word) (x : ℕ → ℝ) (bounds : ℕ → FP.Range.Interval) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, I.decode? (a i) = some (x i))
    (hb : ∀ i ∈ t.leaves, (bounds i).Contains (x i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat I.format) bounds t = some enclosure) :
    ∃ z : ℝ, I.decode? (sumTree I .nearestEven a t).value = some z ∧ enclosure.Contains z ∧
      |z - t.exactSum x| ≤ growth I.format.unitRoundoff t.height * t.mass x +
        (I.format.minSubnormal / 2) * t.roundWeight I.format.unitRoundoff := by
  obtain ⟨q, hq, he, herr⟩ := wordSumTree?_mixed_of_certificate I a x bounds t hx hb hc
  exact ⟨q, decode_of_rat I _ q (sumTree_projection_of_some I a t q hq), he, herr⟩

theorem sequentialSum_mixed_of_certificate (I : Interchange) [I.Valid]
    (a : ℕ → I.Word) (x : ℕ → ℝ) (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat I.format) bounds (sequentialTree 0 n) = some enclosure) :
    ∃ z : ℝ, I.decode? (sequentialSum I .nearestEven a n).value = some z ∧ enclosure.Contains z ∧
      |z - ∑ i ∈ Finset.range n, x i| ≤
        growth I.format.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |x i|) +
        (I.format.minSubnormal / 2) * geomWeight I.format.unitRoundoff (n - 1) := by
  simpa only [sequentialSum, sequentialTree_exactSum, ReductionTree.mass,
    sequentialTree_height, sequentialTree_roundWeight] using
    sumTree_mixed_of_certificate I a x bounds (sequentialTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem pairwiseSum_mixed_of_certificate (I : Interchange) [I.Valid]
    (a : ℕ → I.Word) (x : ℕ → ℝ) (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkSum (.ofFormat I.format) bounds (pairwiseTree 0 n) = some enclosure) :
    ∃ z : ℝ, I.decode? (pairwiseSum I .nearestEven a n).value = some z ∧ enclosure.Contains z ∧
      |z - ∑ i ∈ Finset.range n, x i| ≤
        growth I.format.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
        (I.format.minSubnormal / 2) * (pairwiseTree 0 n).roundWeight I.format.unitRoundoff := by
  simpa only [pairwiseSum, pairwiseTree_exactSum, ReductionTree.mass, pairwiseTree_height] using
    sumTree_mixed_of_certificate I a x bounds (pairwiseTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem dot_mixed_of_certificate (I : Interchange) [I.Valid]
    (a b : ℕ → I.Word) (x y : ℕ → ℝ) (ba bb : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hy : ∀ i < n, I.decode? (b i) = some (y i))
    (ha : ∀ i < n, (ba i).Contains (x i))
    (hb : ∀ i < n, (bb i).Contains (y i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkDot (.ofFormat I.format) ba bb n = some enclosure) :
    ∃ z : ℝ, I.decode? (dot I .nearestEven a b n).value = some z ∧ enclosure.Contains z ∧
      MixedBackwardStable (growth I.format.unitRoundoff (2 * n))
        (dotResidual I.format.unitRoundoff (I.format.minSubnormal / 2) n) x y n z := by
  obtain ⟨q, hq, he, herr⟩ := wordDot?_mixed_of_certificate I a b x y ba bb n hx hy ha hb hc
  exact ⟨q, decode_of_rat I _ q (dot_projection_of_some I a b n q hq), he, herr⟩

theorem dot_mixed_gamma_of_certificate (I : Interchange) [I.Valid]
    (a b : ℕ → I.Word) (x y : ℕ → ℝ) (ba bb : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hy : ∀ i < n, I.decode? (b i) = some (y i))
    (ha : ∀ i < n, (ba i).Contains (x i)) (hb : ∀ i < n, (bb i).Contains (y i))
    {enclosure : FP.Range.Interval}
    (hc : FP.Range.checkDot (.ofFormat I.format) ba bb n = some enclosure)
    (hn : (2 * n : ℕ) * I.format.unitRoundoff < 1) :
    ∃ z : ℝ, I.decode? (dot I .nearestEven a b n).value = some z ∧ enclosure.Contains z ∧
      MixedBackwardStable (gamma I.format.unitRoundoff (2 * n))
        (dotResidual I.format.unitRoundoff (I.format.minSubnormal / 2) n) x y n z := by
  obtain ⟨z, hz, he, herr⟩ := dot_mixed_of_certificate I a b x y ba bb n hx hy ha hb hc
  exact ⟨z, hz, he, herr.mono (growth_le_gamma I.format.unitRoundoff_pos.le _ hn) le_rfl⟩

theorem dot_backward (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hy : ∀ i < n, I.decode? (b i) = some (y i))
    (hs : I.format.SafeDot x y n) (hn : (2 * n : ℕ) * I.format.unitRoundoff < 1) :
    ∃ z : ℝ, I.decode? (dot I .nearestEven a b n).value = some z ∧
      BackwardStable (gamma I.format.unitRoundoff (2 * n)) x y n z := by
  obtain ⟨z, hz, herr⟩ := I.format.innerProduct_backward x y n hs hn
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp ((wordDot?_cast I a b x y n hx hy).trans hz)
  exact ⟨z, hval ▸ decode_of_rat I _ q (dot_projection_of_some I a b n q hq), herr⟩

private theorem trace_of_safe (F : Format) (x : ℕ → ℝ) (t : ReductionTree)
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

private theorem sumTree_decode_of_safe (I : Interchange) [I.Valid] (a : ℕ → I.Word)
    (x : ℕ → ℝ) (t : ReductionTree) (hx : ∀ i ∈ t.leaves, I.decode? (a i) = some (x i))
    (hs : t.Trace I.format.Safe I.format.roundFinite x) :
    I.decode? (sumTree I .nearestEven a t).value = some (t.rounded I.format.roundFinite x) := by
  have hv := (wordSumTree?_cast I a x t hx).trans
    (I.format.sumTree?_eq_of_nonoverflow x t (trace_of_safe I.format x t hs))
  obtain ⟨q, hq, hval⟩ := Option.map_eq_some_iff.mp hv
  exact hval ▸ decode_of_rat I _ q (sumTree_projection_of_some I a t q hq)

theorem sequentialSum_backward (I : Interchange) [I.Valid] (a : ℕ → I.Word) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hs : (sequentialTree 0 n).Trace I.format.Safe I.format.roundFinite x)
    (hn : ((n - 1 : ℕ) : ℝ) * I.format.unitRoundoff < 1) :
    ∃ z : ℝ, I.decode? (sequentialSum I .nearestEven a n).value = some z ∧
      BackwardStable (gamma I.format.unitRoundoff (n - 1)) x (fun _ => 1) n z := by
  refine ⟨_, sumTree_decode_of_safe I a x _ (fun i hi => hx i (by simpa using hi)) hs, ?_⟩
  exact FP.sequentialSum_backward_gamma I.format.unitRoundoff_pos.le I.format.roundFinite I.format.Safe
    (fun _ hz => I.format.roundFinite_relativeError hz) x n hs hn

theorem pairwiseSum_backward (I : Interchange) [I.Valid] (a : ℕ → I.Word) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, I.decode? (a i) = some (x i))
    (hs : (pairwiseTree 0 n).Trace I.format.Safe I.format.roundFinite x)
    (hn : ((Nat.clog 2 n : ℕ) : ℝ) * I.format.unitRoundoff < 1) :
    ∃ z : ℝ, I.decode? (pairwiseSum I .nearestEven a n).value = some z ∧
      BackwardStable (gamma I.format.unitRoundoff (Nat.clog 2 n)) x (fun _ => 1) n z := by
  refine ⟨_, sumTree_decode_of_safe I a x _ (fun i hi => hx i (by simpa using hi)) hs, ?_⟩
  exact FP.pairwiseSum_backward_gamma I.format.unitRoundoff_pos.le I.format.roundFinite I.format.Safe
    (fun _ hz => I.format.roundFinite_relativeError hz) x n hs hn

end FP.IEEE.Software
