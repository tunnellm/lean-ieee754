import FP.IEEE.Software.Reductions

/-! Executable checks and certificate-to-theorem examples without native Float
operations. Real error bounds are obtained from proved refinements, not tests. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software.Tests
open Interchange

private def cancellation32 : ℕ → ℚ
  | 0 => 16777216
  | 1 => 1
  | 2 => 1
  | _ => -16777216

private def cancellation64 : ℕ → ℚ
  | 0 => 9007199254740992
  | 1 => 1
  | 2 => 1
  | _ => -9007199254740992

theorem schedule_difference32 :
    sequentialSum? binary32 cancellation32 4 = some 0 ∧
    pairwiseSum? binary32 cancellation32 4 = some 1 := by decide +kernel

theorem schedule_difference64 :
    sequentialSum? binary64 cancellation64 4 = some 0 ∧
    pairwiseSum? binary64 cancellation64 4 = some 1 := by decide +kernel

theorem empty_and_singleton :
    sequentialSum? binary32 (fun _ => 7) 0 = some 0 ∧
    pairwiseSum? binary64 (fun _ => 7) 0 = some 0 ∧
    sequentialSum? binary32 (fun _ => 7) 1 = some 7 ∧
    pairwiseSum? binary64 (fun _ => 7) 1 = some 7 ∧
    dot? binary32 (fun _ => 7) (fun _ => 9) 0 = some 0 := by decide +kernel

theorem dot_overflow_propagates :
    dot? binary32 (fun _ => (2 : ℚ)^100) (fun _ => (2 : ℚ)^100) 1 = none ∧
    dot? binary64 (fun _ => (2 : ℚ)^600) (fun _ => (2 : ℚ)^600) 2 = none := by
  decide +kernel

theorem word_underflow32 :
    wordDot? fp32 (fun _ => 1#32) (fun _ => 0x3f000000#32) 1 = some 0 := by
  decide +kernel

theorem word_underflow64 :
    wordDot? fp64 (fun _ => 1#64) (fun _ => 0x3fe0000000000000#64) 1 = some 0 := by
  decide +kernel

theorem exceptional_inputs_have_no_finite_projection :
    wordSequentialSum? fp32 (fun _ => 0x7f800000#32) 1 = none ∧
    wordPairwiseSum? fp64 (fun _ => 0x7ff8000000000001#64) 1 = none ∧
    wordDot? fp32 (fun _ => 0x7f800001#32) (fun _ => 0#32) 1 = none := by
  decide +kernel

/-- Only leaves that the schedule actually visits must decode to finite values. -/
theorem unused_exceptional_inputs :
    wordSequentialSum? fp32 (fun _ => 0x7f800000#32) 0 = some 0 ∧
    wordDot? fp64 (fun _ => 0x7ff8000000000001#64) (fun _ => 0#64) 0 = some 0 := by
  decide +kernel

/-- A complete software summation certificate supplies both an executable result
and its mixed forward-error theorem. -/
theorem certified_pairwise32 :
    ∃ q : ℚ, pairwiseSum? binary32 (fun _ => (1 : ℚ)/8) 5 = some q ∧
      |(q : ℝ) - ∑ i ∈ Finset.range 5, ((fun _ => (1 : ℚ)/8) i : ℝ)| ≤
        growth binary32.unitRoundoff (Nat.clog 2 5) *
          (∑ i ∈ Finset.range 5, |((fun _ => (1 : ℚ)/8) i : ℝ)|) +
        (binary32.minSubnormal / 2) * (pairwiseTree 0 5).roundWeight binary32.unitRoundoff := by
  have hc : (FP.Range.checkSum (.ofFormat binary32) (fun _ => ⟨0,1⟩)
      (pairwiseTree 0 5)).isSome = true := by decide +kernel
  obtain ⟨enclosure, he⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨q, hq, _, herr⟩ := pairwiseSum?_mixed_of_certificate binary32
    (fun _ => (1 : ℚ)/8) (fun _ => ⟨0,1⟩) 5
    (by intro i hi; norm_num [FP.Range.Interval.Contains]) he
  exact ⟨q, hq, herr⟩

/-- Underflow is accompanied by a mixed backward theorem, not a false pure-relative claim. -/
theorem certified_underflow64 :
    ∃ q : ℚ, dot? binary64 (fun _ => (2 : ℚ)^(-1074 : ℤ)) (fun _ => (1 : ℚ)/2) 1 = some q ∧
      MixedBackwardStable (growth binary64.unitRoundoff 2)
        (dotResidual binary64.unitRoundoff (binary64.minSubnormal / 2) 1)
        (fun _ => ((2 : ℚ)^(-1074 : ℤ) : ℝ)) (fun _ => ((1 : ℚ)/2 : ℝ)) 1 (q : ℝ) := by
  let ba : ℕ → FP.Range.Interval := fun _ => ⟨0, (2 : ℚ)^(-1074 : ℤ)⟩
  let bb : ℕ → FP.Range.Interval := fun _ => ⟨1/2,1/2⟩
  have hc : (FP.Range.checkDot (.ofFormat binary64) ba bb 1).isSome = true := by decide +kernel
  obtain ⟨enclosure, he⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨q, hq, _, herr⟩ := dot?_mixed_of_certificate binary64
    (fun _ => (2 : ℚ)^(-1074 : ℤ)) (fun _ => (1 : ℚ)/2) ba bb 1
    (by
      intro i hi
      constructor
      · exact Rat.cast_le.mpr (show (0 : ℚ) ≤ 2 ^ (-1074 : ℤ) from
          le_of_lt (zpow_pos (by norm_num) _))
      · exact le_rfl)
    (by intro i hi; norm_num [bb, FP.Range.Interval.Contains]) he
  exact ⟨q, hq, by simpa using herr⟩

end FP.IEEE.Software.Tests
