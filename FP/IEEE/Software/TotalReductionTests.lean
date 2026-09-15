import FP.IEEE.Software.TotalReductionBounds

/-! Kernel checks on actual total reductions, plus a certificate-to-bound example. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests
open Interchange

private def flags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags

private def cancellationWords32 : ℕ → fp32.Word
  | 0 => 0x4b800000
  | 1 | 2 => 0x3f800000
  | _ => 0xcb800000
private def cancellationWords64 : ℕ → fp64.Word
  | 0 => 0x4340000000000000
  | 1 | 2 => 0x3ff0000000000000
  | _ => 0xc340000000000000

example : (sequentialSum fp32 .nearestEven cancellationWords32 4).value = 0#32 ∧
    (pairwiseSum fp32 .nearestEven cancellationWords32 4).value = 0x3f800000#32 ∧
    flags (pairwiseSum fp32 .nearestEven cancellationWords32 4) =
      [false, false, false, false, true] := by decide +kernel

example : (sequentialSum fp64 .nearestEven cancellationWords64 4).value = 0#64 ∧
    (pairwiseSum fp64 .nearestEven cancellationWords64 4).value = 0x3ff0000000000000#64 := by decide +kernel

/-- Empty schedules do not inspect exceptional inputs. Singleton sums are copies. -/
example : (sequentialSum fp32 .nearestEven (fun _ => 0x7f800001) 0).value = 0#32 ∧
    flags (dot fp64 .nearestEven (fun _ => 0x7ff0000000000001) (fun _ => 0) 0) =
      [false, false, false, false, false] ∧
    (pairwiseSum fp32 .nearestEven (fun _ => 0xff800123) 1).value = 0xff800123#32 ∧
    flags (pairwiseSum fp32 .nearestEven (fun _ => 0xff800123) 1) =
      [false, false, false, false, false] := by decide +kernel

/-- A used signaling NaN is quieted by arithmetic, with payload/sign retained. -/
example : (sequentialSum fp64 .nearestEven (fun i => if i = 0 then 0xfff0000000000123 else 0) 2).value =
    0xfff8000000000123#64 ∧
    flags (dot fp32 .nearestEven (fun _ => 0x7f800123) (fun _ => 0x3f800000) 1) =
      [true, false, false, false, false] := by decide +kernel

/-- Overflow is followed by invalid; both flags survive the resulting NaN. -/
example : flags (sequentialSum fp32 .nearestEven
    (fun i => if i < 2 then 0x7f7fffff else 0xff800000) 3) =
      [true, false, true, false, true] ∧
    (sequentialSum fp32 .nearestEven
      (fun i => if i < 2 then 0x7f7fffff else 0xff800000) 3).value = 0x7fc00000#32 := by decide +kernel

example : flags (dot fp64 .nearestEven
    (fun i => if i = 0 then 0x7fefffffffffffff else 0xffefffffffffffff)
    (fun _ => 0x4000000000000000) 2) = [true, false, true, false, true] := by decide +kernel

/-- Underflow in a product remains visible after the exact accumulator addition. -/
example : (dot fp64 .nearestEven (fun _ => 1) (fun _ => 0x3fe0000000000000) 1).value = 0#64 ∧
    flags (dot fp64 .nearestEven (fun _ => 1) (fun _ => 0x3fe0000000000000) 1) =
      [false, false, false, true, true] ∧
    (dot fp32 .towardPositive (fun _ => 1) (fun _ => 0x3f000000) 1).value = 1#32 := by decide +kernel

/-- Cancellation zero obeys the selected mode throughout the schedule. -/
example : (sequentialSum fp32 .towardNegative
    (fun i => if i = 0 then 0x3f800000 else 0xbf800000) 2).value = 0x80000000#32 ∧
    (dot fp64 .towardNegative (fun _ => 0x8000000000000000)
      (fun _ => 0x3ff0000000000000) 1).value = 0x8000000000000000#64 := by decide +kernel

/-- A checked interval certificate supplies a theorem about the total result word. -/
theorem certified_total_pairwise32 :
    ∃ z : ℝ, fp32.decode? (pairwiseSum fp32 .nearestEven (fun _ => 0x3e000000) 5).value = some z ∧
      |z - ∑ i ∈ Finset.range 5, ((fun _ => (1 : ℝ)/8) i)| ≤
        growth binary32.unitRoundoff (Nat.clog 2 5) *
          (∑ i ∈ Finset.range 5, |((fun _ => (1 : ℝ)/8) i)|) +
        (binary32.minSubnormal / 2) * (pairwiseTree 0 5).roundWeight binary32.unitRoundoff := by
  have hc : (FP.Range.checkSum (.ofFormat binary32) (fun _ => ⟨0,1⟩)
      (pairwiseTree 0 5)).isSome = true := by decide +kernel
  obtain ⟨enclosure, he⟩ := Option.isSome_iff_exists.mp hc
  have hq : (Datum.decode fp32 0x3e000000).toRat? = some ((1 : ℚ)/8) := by decide +kernel
  have hv := Datum.toRat?_decode fp32 0x3e000000
  rw [hq] at hv
  have hx : fp32.decode? 0x3e000000 = some ((1 : ℝ)/8) := by simpa using hv.symm
  obtain ⟨z, hz, _, herr⟩ := pairwiseSum_mixed_of_certificate fp32
    (fun _ => 0x3e000000) (fun _ => (1 : ℝ)/8) (fun _ => ⟨0,1⟩) 5
    (fun _ _ => hx) (by intro i hi; norm_num [FP.Range.Interval.Contains]) he
  exact ⟨z, hz, herr⟩

end FP.IEEE.Software.Tests
