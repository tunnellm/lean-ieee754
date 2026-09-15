import FP.Native.Bridge
import FP.IEEE.Summation
import FP.Range.Checker

namespace FP.Native

def floatTreeSum (a : ℕ → Float) (t : ReductionTree) : Float :=
  t.eval (Float.ofBits 0) (· + ·) a
def float32TreeSum (a : ℕ → Float32) (t : ReductionTree) : Float32 :=
  t.eval (Float32.ofBits 0) (· + ·) a

def floatSequentialSum (a : ℕ → Float) (n : ℕ) : Float := floatTreeSum a (sequentialTree 0 n)
def floatPairwiseSum (a : ℕ → Float) (n : ℕ) : Float := floatTreeSum a (pairwiseTree 0 n)
def float32SequentialSum (a : ℕ → Float32) (n : ℕ) : Float32 := float32TreeSum a (sequentialTree 0 n)
def float32PairwiseSum (a : ℕ → Float32) (n : ℕ) : Float32 := float32TreeSum a (pairwiseTree 0 n)

noncomputable section
open scoped BigOperators

theorem nativeTree_value {α : Type} (F : FP.IEEE.Format)
    (zero : α) (add : α → α → α) (value : α → Option ℝ)
    (hz : value zero = some 0)
    (ha : ∀ a b x y, value a = some x → value b = some y →
      |x + y| < F.overflowThreshold → value (add a b) = F.round? (x + y))
    (a : ℕ → α) (x : ℕ → ℝ) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, value (a i) = some (x i))
    (hs : t.Trace (fun z => |z| < F.overflowThreshold) F.roundFinite x) :
    value (t.eval zero add a) = some (t.rounded F.roundFinite x) := by
  induction t with
  | zero => exact hz
  | input i => exact hx i (by simp [ReductionTree.leaves])
  | add l r hl hr =>
    have hvL := hl (fun i hi => hx i (by simp [ReductionTree.leaves, hi])) hs.1
    have hvR := hr (fun i hi => hx i (by simp [ReductionTree.leaves, hi])) hs.2.1
    rw [ReductionTree.eval, ha _ _ _ _ hvL hvR hs.2.2,
      FP.IEEE.Format.round?, if_pos hs.2.2]
    rfl

/-- Certificate success discharges every operation-range obligation. -/
theorem nativeTree_mixed_of_certificate {α : Type} (F : FP.IEEE.Format)
    (zero : α) (add : α → α → α) (value : α → Option ℝ)
    (hz : value zero = some 0)
    (ha : ∀ a b x y, value a = some x → value b = some y →
      |x + y| < F.overflowThreshold → value (add a b) = F.round? (x + y))
    (a : ℕ → α) (x : ℕ → ℝ) (bounds : ℕ → FP.Range.Interval) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, value (a i) = some (x i))
    (hb : ∀ i ∈ t.leaves, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat F) bounds t).isSome = true) :
    ∃ s : ℝ, value (t.eval zero add a) = some s ∧
      |s - t.exactSum x| ≤ growth F.unitRoundoff t.height * t.mass x +
        (F.minSubnormal / 2) * t.roundWeight F.unitRoundoff := by
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨htrace, _⟩ := FP.Range.checkSum_sound F bounds x t hb hI
  exact ⟨t.rounded F.roundFinite x, nativeTree_value F zero add value hz ha a x t hx htrace,
    F.sumTree_mixed_error x t⟩

theorem floatTreeSum_equiv (a : ℕ → Float) (x : ℕ → ℝ) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, floatValue (a i) = some (x i))
    (hs : t.Trace (fun z => |z| < FP.IEEE.binary64.overflowThreshold) FP.IEEE.binary64.roundFinite x) :
    floatValue (floatTreeSum a t) = FP.IEEE.binary64.sumTree? x t :=
  (nativeTree_value _ _ _ _ floatValue_zero float_add_equiv a x t hx hs).trans
    (FP.IEEE.binary64.sumTree?_eq_of_nonoverflow x t hs).symm

theorem floatSequentialSum_equiv (a : ℕ → Float) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hs : (sequentialTree 0 n).Trace (fun z => |z| < FP.IEEE.binary64.overflowThreshold) FP.IEEE.binary64.roundFinite x) :
    floatValue (floatSequentialSum a n) = FP.IEEE.binary64.sequentialSum? x n :=
  floatTreeSum_equiv a x _ (fun i hi => hx i (by simpa using hi)) hs

theorem floatSequentialSum_mixed_of_certificate (a : ℕ → Float) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary64) bounds (sequentialTree 0 n)).isSome = true) :
    ∃ s : ℝ, floatValue (floatSequentialSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        growth FP.IEEE.binary64.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary64.minSubnormal / 2) * (geomWeight FP.IEEE.binary64.unitRoundoff (n - 1)) := by
  simpa only [floatSequentialSum, floatTreeSum, sequentialTree_exactSum, ReductionTree.mass, sequentialTree_height, sequentialTree_roundWeight] using
    nativeTree_mixed_of_certificate FP.IEEE.binary64 _ _ _ floatValue_zero float_add_equiv a x bounds (sequentialTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem floatSequentialSum_mixed_gamma_of_certificate (a : ℕ → Float) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary64) bounds (sequentialTree 0 n)).isSome = true)
    (hn : ((n - 1 : ℕ) : ℝ) * FP.IEEE.binary64.unitRoundoff < 1) :
    ∃ s : ℝ, floatValue (floatSequentialSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        gamma FP.IEEE.binary64.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary64.minSubnormal / 2) * (geomWeight FP.IEEE.binary64.unitRoundoff (n - 1)) := by
  obtain ⟨s, hv, he⟩ := floatSequentialSum_mixed_of_certificate a x bounds n hx hb hc
  exact ⟨s, hv, he.trans (add_le_add
    (mul_le_mul_of_nonneg_right (growth_le_gamma FP.IEEE.binary64.unitRoundoff_pos.le _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)⟩

theorem floatPairwiseSum_equiv (a : ℕ → Float) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hs : (pairwiseTree 0 n).Trace (fun z => |z| < FP.IEEE.binary64.overflowThreshold) FP.IEEE.binary64.roundFinite x) :
    floatValue (floatPairwiseSum a n) = FP.IEEE.binary64.pairwiseSum? x n :=
  floatTreeSum_equiv a x _ (fun i hi => hx i (by simpa using hi)) hs

theorem floatPairwiseSum_mixed_of_certificate (a : ℕ → Float) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary64) bounds (pairwiseTree 0 n)).isSome = true) :
    ∃ s : ℝ, floatValue (floatPairwiseSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        growth FP.IEEE.binary64.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary64.minSubnormal / 2) * ((pairwiseTree 0 n).roundWeight FP.IEEE.binary64.unitRoundoff) := by
  simpa only [floatPairwiseSum, floatTreeSum, pairwiseTree_exactSum, ReductionTree.mass, pairwiseTree_height] using
    nativeTree_mixed_of_certificate FP.IEEE.binary64 _ _ _ floatValue_zero float_add_equiv a x bounds (pairwiseTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem floatPairwiseSum_mixed_gamma_of_certificate (a : ℕ → Float) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary64) bounds (pairwiseTree 0 n)).isSome = true)
    (hn : ((Nat.clog 2 n) : ℝ) * FP.IEEE.binary64.unitRoundoff < 1) :
    ∃ s : ℝ, floatValue (floatPairwiseSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        gamma FP.IEEE.binary64.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary64.minSubnormal / 2) * ((pairwiseTree 0 n).roundWeight FP.IEEE.binary64.unitRoundoff) := by
  obtain ⟨s, hv, he⟩ := floatPairwiseSum_mixed_of_certificate a x bounds n hx hb hc
  exact ⟨s, hv, he.trans (add_le_add
    (mul_le_mul_of_nonneg_right (growth_le_gamma FP.IEEE.binary64.unitRoundoff_pos.le _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)⟩

theorem float32TreeSum_equiv (a : ℕ → Float32) (x : ℕ → ℝ) (t : ReductionTree)
    (hx : ∀ i ∈ t.leaves, float32Value (a i) = some (x i))
    (hs : t.Trace (fun z => |z| < FP.IEEE.binary32.overflowThreshold) FP.IEEE.binary32.roundFinite x) :
    float32Value (float32TreeSum a t) = FP.IEEE.binary32.sumTree? x t :=
  (nativeTree_value _ _ _ _ float32Value_zero float32_add_equiv a x t hx hs).trans
    (FP.IEEE.binary32.sumTree?_eq_of_nonoverflow x t hs).symm

theorem float32SequentialSum_equiv (a : ℕ → Float32) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hs : (sequentialTree 0 n).Trace (fun z => |z| < FP.IEEE.binary32.overflowThreshold) FP.IEEE.binary32.roundFinite x) :
    float32Value (float32SequentialSum a n) = FP.IEEE.binary32.sequentialSum? x n :=
  float32TreeSum_equiv a x _ (fun i hi => hx i (by simpa using hi)) hs

theorem float32SequentialSum_mixed_of_certificate (a : ℕ → Float32) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary32) bounds (sequentialTree 0 n)).isSome = true) :
    ∃ s : ℝ, float32Value (float32SequentialSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        growth FP.IEEE.binary32.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary32.minSubnormal / 2) * (geomWeight FP.IEEE.binary32.unitRoundoff (n - 1)) := by
  simpa only [float32SequentialSum, float32TreeSum, sequentialTree_exactSum, ReductionTree.mass, sequentialTree_height, sequentialTree_roundWeight] using
    nativeTree_mixed_of_certificate FP.IEEE.binary32 _ _ _ float32Value_zero float32_add_equiv a x bounds (sequentialTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem float32SequentialSum_mixed_gamma_of_certificate (a : ℕ → Float32) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary32) bounds (sequentialTree 0 n)).isSome = true)
    (hn : ((n - 1 : ℕ) : ℝ) * FP.IEEE.binary32.unitRoundoff < 1) :
    ∃ s : ℝ, float32Value (float32SequentialSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        gamma FP.IEEE.binary32.unitRoundoff (n - 1) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary32.minSubnormal / 2) * (geomWeight FP.IEEE.binary32.unitRoundoff (n - 1)) := by
  obtain ⟨s, hv, he⟩ := float32SequentialSum_mixed_of_certificate a x bounds n hx hb hc
  exact ⟨s, hv, he.trans (add_le_add
    (mul_le_mul_of_nonneg_right (growth_le_gamma FP.IEEE.binary32.unitRoundoff_pos.le _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)⟩

theorem float32PairwiseSum_equiv (a : ℕ → Float32) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hs : (pairwiseTree 0 n).Trace (fun z => |z| < FP.IEEE.binary32.overflowThreshold) FP.IEEE.binary32.roundFinite x) :
    float32Value (float32PairwiseSum a n) = FP.IEEE.binary32.pairwiseSum? x n :=
  float32TreeSum_equiv a x _ (fun i hi => hx i (by simpa using hi)) hs

theorem float32PairwiseSum_mixed_of_certificate (a : ℕ → Float32) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary32) bounds (pairwiseTree 0 n)).isSome = true) :
    ∃ s : ℝ, float32Value (float32PairwiseSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        growth FP.IEEE.binary32.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary32.minSubnormal / 2) * ((pairwiseTree 0 n).roundWeight FP.IEEE.binary32.unitRoundoff) := by
  simpa only [float32PairwiseSum, float32TreeSum, pairwiseTree_exactSum, ReductionTree.mass, pairwiseTree_height] using
    nativeTree_mixed_of_certificate FP.IEEE.binary32 _ _ _ float32Value_zero float32_add_equiv a x bounds (pairwiseTree 0 n)
      (fun i hi => hx i (by simpa using hi)) (fun i hi => hb i (by simpa using hi)) hc

theorem float32PairwiseSum_mixed_gamma_of_certificate (a : ℕ → Float32) (x : ℕ → ℝ)
    (bounds : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hb : ∀ i < n, (bounds i).Contains (x i))
    (hc : (FP.Range.checkSum (.ofFormat FP.IEEE.binary32) bounds (pairwiseTree 0 n)).isSome = true)
    (hn : ((Nat.clog 2 n) : ℝ) * FP.IEEE.binary32.unitRoundoff < 1) :
    ∃ s : ℝ, float32Value (float32PairwiseSum a n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i| ≤
        gamma FP.IEEE.binary32.unitRoundoff (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
          (FP.IEEE.binary32.minSubnormal / 2) * ((pairwiseTree 0 n).roundWeight FP.IEEE.binary32.unitRoundoff) := by
  obtain ⟨s, hv, he⟩ := float32PairwiseSum_mixed_of_certificate a x bounds n hx hb hc
  exact ⟨s, hv, he.trans (add_le_add
    (mul_le_mul_of_nonneg_right (growth_le_gamma FP.IEEE.binary32.unitRoundoff_pos.le _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)⟩

end
end FP.Native
