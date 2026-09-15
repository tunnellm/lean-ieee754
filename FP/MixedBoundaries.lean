import FP.Native.Summation
import FP.Native.MixedDot
import FP.IEEE.Boundaries

/-! Kernel-checked certificate and boundary examples for the public APIs. -/
namespace FP.Examples
open FP.Native FP.Range
open scoped BigOperators

example : (sequentialTree 0 0).leaves = [] := rfl
example : (pairwiseTree 0 1).leaves = [0] := by decide +kernel
example : (pairwiseTree 0 3).leaves = [0, 1, 2] := by decide +kernel
example : (pairwiseTree 0 5).leaves = [0, 1, 2, 3, 4] := by decide +kernel
example : (pairwiseTree 0 5).height = 3 ∧ (sequentialTree 0 5).height = 4 := by decide +kernel

example (a : ℕ → Float) : floatValue (floatSequentialSum a 0) = some 0 := floatValue_zero
example (a : ℕ → Float32) : float32Value (float32PairwiseSum a 0) = some 0 := by
  simp [float32PairwiseSum, float32TreeSum, pairwiseTree, ReductionTree.eval, float32Value_zero]
example (a : ℕ → Float) : floatPairwiseSum a 1 = a 0 := by
  simp [floatPairwiseSum, floatTreeSum, pairwiseTree, ReductionTree.eval]
example (a : ℕ → Float32) : float32SequentialSum a 1 = a 0 := rfl

example : MixedError 0 1 (3 : ℝ) 4 := by norm_num [MixedError]
example : MixedError (1/8) 0 (8 : ℝ) 9 := by norm_num [MixedError]
example : geomWeight 0 5 = 5 := by norm_num [geomWeight, Finset.sum_range_succ]

/-- Concrete rational checks, including the large binary64 subnormal denominator. -/
example : (checkSum (.ofFormat IEEE.binary32) (fun _ => ⟨-1, 1⟩) (sequentialTree 0 5)).isSome = true := by decide +kernel
example : (checkSum (.ofFormat IEEE.binary64) (fun _ => ⟨-1, 1⟩) (pairwiseTree 0 5)).isSome = true := by decide +kernel
example : checkSum (.ofFormat IEEE.binary32) (fun _ => ⟨1, -1⟩) (sequentialTree 0 1) = none := by decide +kernel
example : checkDot (.ofFormat IEEE.binary64) (fun _ => ⟨1, -1⟩) (fun _ => ⟨0, 0⟩) 1 = none := by decide +kernel

example : checkRound (.ofFormat IEEE.binary32)
    ⟨(Params.ofFormat IEEE.binary32).threshold, (Params.ofFormat IEEE.binary32).threshold⟩ = none := by decide +kernel
example : checkRound (.ofFormat IEEE.binary64)
    ⟨(Params.ofFormat IEEE.binary64).threshold, (Params.ofFormat IEEE.binary64).threshold⟩ = none := by decide +kernel

/-- Rejection does not imply overflow for every enclosed input: zero rounds to zero. -/
example : let T := (Params.ofFormat IEEE.binary32).threshold
    checkRound (.ofFormat IEEE.binary32) ⟨-T, T⟩ = none ∧
      (⟨-T, T⟩ : Interval).Contains 0 ∧ IEEE.binary32.round? 0 = some 0 := by
  refine ⟨by decide +kernel, ?_, IEEE.binary32.round?_zero⟩
  have hp := IEEE.binary32.overflowThreshold_pos
  simp only [Interval.Contains, Rat.cast_neg, Params.ofFormat_threshold]
  constructor <;> linarith

/-- Signed interval multiplication encloses all four corner products. -/
example : (Interval.mul ⟨-2, 3⟩ ⟨-4, 5⟩) = ⟨-12, 15⟩ := by decide +kernel

private theorem float_one : floatValue (Float.ofBits 0x3ff0000000000000) = some 1 := by
  change some ((4503599627370496 : ℝ) * (2 : ℝ) ^ (-52 : ℤ)) = _
  norm_num

private theorem float_half : floatValue (Float.ofBits 0x3fe0000000000000) = some (1/2 : ℝ) := by
  change some ((4503599627370496 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) = _
  norm_num

private theorem float_least : floatValue (Float.ofBits 1) = some IEEE.binary64.minSubnormal := by
  rw [floatValue_decode]
  change IEEE.fp64.decode? (1 : IEEE.fp64.Word) = _
  rw [IEEE.fp64.decode?_eq _ (by decide)]
  have hm : IEEE.fp64.mantissa (1 : IEEE.fp64.Word) = 1 := by decide
  have he : IEEE.fp64.scaleExponent (1 : IEEE.fp64.Word) = -1074 := by decide
  have hs : IEEE.fp64.negative (1 : IEEE.fp64.Word) = false := by decide
  simp only [IEEE.Interchange.value, hm, he, hs, Bool.false_eq_true, if_false, Nat.cast_one, one_mul]
  norm_num [IEEE.Format.minSubnormal, IEEE.binary64]

/-- A native five-term sum certified only from finite inputs and input intervals. -/
theorem float_pairwise_certified :
    ∃ s : ℝ, floatValue (floatPairwiseSum (fun _ => Float.ofBits 0x3ff0000000000000) 5) = some s ∧
      |s - 5| ≤ growth IEEE.binary64.unitRoundoff (Nat.clog 2 5) * 5 +
        (IEEE.binary64.minSubnormal / 2) * (pairwiseTree 0 5).roundWeight IEEE.binary64.unitRoundoff := by
  have hc : (checkSum (.ofFormat IEEE.binary64) (fun _ => (⟨-1, 1⟩ : Interval))
      (pairwiseTree 0 5)).isSome = true := by decide +kernel
  simpa using floatPairwiseSum_mixed_of_certificate (fun _ => Float.ofBits 0x3ff0000000000000)
    (fun _ => 1) (fun _ => ⟨-1, 1⟩) 5 (fun _ _ => float_one)
    (fun _ _ => by norm_num [Interval.Contains]) hc

theorem float_sequential_certified :
    ∃ s : ℝ, floatValue (floatSequentialSum (fun _ => Float.ofBits 0x3ff0000000000000) 5) = some s ∧
      |s - 5| ≤ growth IEEE.binary64.unitRoundoff 4 * 5 +
        (IEEE.binary64.minSubnormal / 2) * geomWeight IEEE.binary64.unitRoundoff 4 := by
  simpa using floatSequentialSum_mixed_of_certificate (fun _ => Float.ofBits 0x3ff0000000000000)
    (fun _ => 1) (fun _ => ⟨-1, 1⟩) 5 (fun _ _ => float_one)
    (fun _ _ => by norm_num [Interval.Contains]) (by decide +kernel)

/-- The underflow counterexample now has a certified mixed backward explanation. -/
theorem float_underflow_mixed :
    MixedBackwardStable (growth IEEE.binary64.unitRoundoff 2)
      (dotResidual IEEE.binary64.unitRoundoff (IEEE.binary64.minSubnormal / 2) 1)
      (fun _ => IEEE.binary64.minSubnormal) (fun _ => 1/2) 1 0 := by
  let bx : ℕ → Interval := fun _ => ⟨(2 : ℚ)^(-1074 : ℤ), (2 : ℚ)^(-1074 : ℤ)⟩
  let bys : ℕ → Interval := fun _ => ⟨1/2, 1/2⟩
  have hc : (checkDot (.ofFormat IEEE.binary64) bx bys 1).isSome = true := by decide +kernel
  obtain ⟨s, hv, he⟩ := floatDot_mixed_of_certificate
    (fun _ => Float.ofBits 1) (fun _ => Float.ofBits 0x3fe0000000000000)
    (fun _ => IEEE.binary64.minSubnormal) (fun _ => 1/2) bx bys 1
    (fun _ _ => float_least) (fun _ _ => float_half)
    (fun _ _ => by simp [bx, Interval.Contains, IEEE.Format.minSubnormal, IEEE.binary64])
    (fun _ _ => by norm_num [bys, Interval.Contains]) hc
  have hz : floatValue (floatDot (fun _ => Float.ofBits 1)
      (fun _ => Float.ofBits 0x3fe0000000000000) 1) = some 0 := rfl
  have hs : s = 0 := Option.some.inj (hv.symm.trans hz)
  simpa only [hs] using he

example : ¬ BackwardStable (1/2) (fun _ => IEEE.binary64.minSubnormal) (fun _ => 1/2) 1 0 :=
  IEEE.binary64.underflow_not_backwardStable (by norm_num)

private theorem float32_one : float32Value (Float32.ofBits 0x3f800000) = some 1 := by
  change some ((8388608 : ℝ) * (2 : ℝ) ^ (-23 : ℤ)) = _
  norm_num

private theorem float32_half : float32Value (Float32.ofBits 0x3f000000) = some (1/2 : ℝ) := by
  change some ((8388608 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) = _
  norm_num

private theorem float32_least : float32Value (Float32.ofBits 1) = some IEEE.binary32.minSubnormal := by
  rw [float32Value_decode]
  change IEEE.fp32.decode? (1 : IEEE.fp32.Word) = _
  rw [IEEE.fp32.decode?_eq _ (by decide)]
  have hm : IEEE.fp32.mantissa (1 : IEEE.fp32.Word) = 1 := by decide
  have he : IEEE.fp32.scaleExponent (1 : IEEE.fp32.Word) = -149 := by decide
  have hs : IEEE.fp32.negative (1 : IEEE.fp32.Word) = false := by decide
  simp only [IEEE.Interchange.value, hm, he, hs, Bool.false_eq_true, if_false, Nat.cast_one, one_mul]
  norm_num [IEEE.Format.minSubnormal, IEEE.binary32]

/-- A native five-term sum certified only from finite inputs and input intervals. -/
theorem float32_pairwise_certified :
    ∃ s : ℝ, float32Value (float32PairwiseSum (fun _ => Float32.ofBits 0x3f800000) 5) = some s ∧
      |s - 5| ≤ growth IEEE.binary32.unitRoundoff (Nat.clog 2 5) * 5 +
        (IEEE.binary32.minSubnormal / 2) * (pairwiseTree 0 5).roundWeight IEEE.binary32.unitRoundoff := by
  have hc : (checkSum (.ofFormat IEEE.binary32) (fun _ => (⟨-1, 1⟩ : Interval))
      (pairwiseTree 0 5)).isSome = true := by decide +kernel
  simpa using float32PairwiseSum_mixed_of_certificate (fun _ => Float32.ofBits 0x3f800000)
    (fun _ => 1) (fun _ => ⟨-1, 1⟩) 5 (fun _ _ => float32_one)
    (fun _ _ => by norm_num [Interval.Contains]) hc

theorem float32_sequential_certified :
    ∃ s : ℝ, float32Value (float32SequentialSum (fun _ => Float32.ofBits 0x3f800000) 5) = some s ∧
      |s - 5| ≤ growth IEEE.binary32.unitRoundoff 4 * 5 +
        (IEEE.binary32.minSubnormal / 2) * geomWeight IEEE.binary32.unitRoundoff 4 := by
  simpa using float32SequentialSum_mixed_of_certificate (fun _ => Float32.ofBits 0x3f800000)
    (fun _ => 1) (fun _ => ⟨-1, 1⟩) 5 (fun _ _ => float32_one)
    (fun _ _ => by norm_num [Interval.Contains]) (by decide +kernel)

/-- The underflow counterexample now has a certified mixed backward explanation. -/
theorem float32_underflow_mixed :
    MixedBackwardStable (growth IEEE.binary32.unitRoundoff 2)
      (dotResidual IEEE.binary32.unitRoundoff (IEEE.binary32.minSubnormal / 2) 1)
      (fun _ => IEEE.binary32.minSubnormal) (fun _ => 1/2) 1 0 := by
  let bx : ℕ → Interval := fun _ => ⟨(2 : ℚ)^(-149 : ℤ), (2 : ℚ)^(-149 : ℤ)⟩
  let bys : ℕ → Interval := fun _ => ⟨1/2, 1/2⟩
  have hc : (checkDot (.ofFormat IEEE.binary32) bx bys 1).isSome = true := by decide +kernel
  obtain ⟨s, hv, he⟩ := float32Dot_mixed_of_certificate
    (fun _ => Float32.ofBits 1) (fun _ => Float32.ofBits 0x3f000000)
    (fun _ => IEEE.binary32.minSubnormal) (fun _ => 1/2) bx bys 1
    (fun _ _ => float32_least) (fun _ _ => float32_half)
    (fun _ _ => by simp [bx, Interval.Contains, IEEE.Format.minSubnormal, IEEE.binary32])
    (fun _ _ => by norm_num [bys, Interval.Contains]) hc
  have hz : float32Value (float32Dot (fun _ => Float32.ofBits 1)
      (fun _ => Float32.ofBits 0x3f000000) 1) = some 0 := rfl
  have hs : s = 0 := Option.some.inj (hv.symm.trans hz)
  simpa only [hs] using he

example : ¬ BackwardStable (1/2) (fun _ => IEEE.binary32.minSubnormal) (fun _ => 1/2) 1 0 :=
  IEEE.binary32.underflow_not_backwardStable (by norm_num)

/-- Cancellation is admitted without any lower bound on the intermediate sum. -/
theorem float32_cancellation_certified :
    let a : ℕ → Float32 := fun i => if i = 0 then Float32.ofBits 0x3f800000 else Float32.ofBits 0xbf800000
    ∃ s : ℝ, float32Value (float32PairwiseSum a 2) = some s ∧
      |s| ≤ growth IEEE.binary32.unitRoundoff 1 * 2 + IEEE.binary32.minSubnormal / 2 := by
  dsimp only
  have hneg : float32Value (Float32.ofBits 0xbf800000) = some (-1 : ℝ) := by
    rw [float32Value_decode]
    change IEEE.fp32.decode? (0xbf800000 : IEEE.fp32.Word) = _
    rw [IEEE.fp32.decode?_eq _ (by decide)]
    have hm : IEEE.fp32.mantissa (0xbf800000 : IEEE.fp32.Word) = 8388608 := by decide
    have he : IEEE.fp32.scaleExponent (0xbf800000 : IEEE.fp32.Word) = -23 := by decide
    have hs : IEEE.fp32.negative (0xbf800000 : IEEE.fp32.Word) = true := by decide
    simp only [IEEE.Interchange.value, hm, he, hs, if_true, Nat.cast_ofNat]
    norm_num
  have hx : ∀ i < 2,
      float32Value ((fun i => if i = 0 then Float32.ofBits 0x3f800000 else Float32.ofBits 0xbf800000) i) =
        some ((fun i => if i = 0 then (1 : ℝ) else -1) i) := by
    intro i _
    by_cases hi : i = 0
    · simpa only [hi, if_true] using float32_one
    · simpa only [hi, if_false] using hneg
  have hb : ∀ i < 2, (⟨-1, 1⟩ : Interval).Contains (if i = 0 then (1 : ℝ) else -1) := by
    intro i _
    split_ifs <;> norm_num [Interval.Contains]
  obtain ⟨s, hv, he⟩ := float32PairwiseSum_mixed_of_certificate _
    (fun i => if i = 0 then (1 : ℝ) else -1) (fun _ => ⟨-1, 1⟩) 2 hx hb (by decide +kernel)
  refine ⟨s, hv, ?_⟩
  have ht : pairwiseTree 0 2 = .add (.input 0) (.input 1) := by decide +kernel
  have hh : Nat.clog 2 2 = 1 := by decide +kernel
  norm_num [Finset.sum_range_succ, ht, hh, ReductionTree.roundWeight] at he
  convert he using 1
  norm_num [IEEE.Format.unitRoundoff, IEEE.binary32]

example : float32Value (float32PairwiseSum
    (fun i => if i = 0 then Float32.ofBits 0x3f800000 else Float32.ofBits 0xbf800000) 2) = some 0 := by
  simp [float32PairwiseSum, float32TreeSum, pairwiseTree, ReductionTree.eval]
  rfl

/-- Three least subnormals are accepted by the public native summation theorem. -/
theorem float32_subnormal_sum_certified :
    ∃ s : ℝ, float32Value (float32PairwiseSum (fun _ => Float32.ofBits 1) 3) = some s ∧
      |s - 3 * IEEE.binary32.minSubnormal| ≤
        growth IEEE.binary32.unitRoundoff (Nat.clog 2 3) * (3 * |IEEE.binary32.minSubnormal|) +
          (IEEE.binary32.minSubnormal / 2) * (pairwiseTree 0 3).roundWeight IEEE.binary32.unitRoundoff := by
  let bounds : ℕ → Interval := fun _ => ⟨(2 : ℚ)^(-149 : ℤ), (2 : ℚ)^(-149 : ℤ)⟩
  have hc : (checkSum (.ofFormat IEEE.binary32) bounds (pairwiseTree 0 3)).isSome = true := by decide +kernel
  simpa using float32PairwiseSum_mixed_of_certificate (fun _ => Float32.ofBits 1)
    (fun _ => IEEE.binary32.minSubnormal) bounds 3 (fun _ _ => float32_least)
    (fun _ _ => by simp [bounds, Interval.Contains, IEEE.Format.minSubnormal, IEEE.binary32]) hc

end FP.Examples
