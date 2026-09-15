import FP.IEEE.Software.CompensatedExecution

/-! Kernel regressions for TwoSum and end-to-end compensated summation certificates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
private def compensationFlags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags

example : (certifiedTwoSum? fp32 0x3f800000 0x33800000).map (fun r => r.value) =
    some (0x3f800000#32,0x33800000#32) ∧
    (certifiedTwoSum? fp32 0x33800000 0x3f800000).map (fun r => r.value) =
      some (0x3f800000#32,0x33800000#32) := by decide +kernel

/-- bvirt may be inexact; requiring all residual-stage flags to be clear would reject this. -/
example : (twoSumTrace fp32 0xbf800000 0x4c000000).bvirt.flags .inexact = true ∧
    (certifiedTwoSum? fp32 0xbf800000 0x4c000000).map (fun r => r.value) =
      some (0x4c000000#32,0xbf800000#32) ∧
    (certifiedTwoSum? fp64 0xbff0000000000000 0x4350000000000000).map (fun r => r.value) =
      some (0x4350000000000000#64,0xbff0000000000000#64) := by decide +kernel

example : (certifiedTwoSum? fp32 1 1).map (fun r => r.value) = some (2#32,0#32) ∧
    (certifiedTwoSum? fp64 0x8000000000000000 0x8000000000000000).map (fun r => r.value) =
      some (0x8000000000000000#64,0#64) ∧
    (certifiedTwoSum? fp32 0x7f7fffff 0x7f7fffff).isNone = true ∧
    (certifiedTwoSum? fp32 0x7fc00123 0x3f800000).isNone = true ∧
    (twoSum fp32 0x7f7fffff 0x7f7fffff).flags .overflow = true ∧
    (twoSum fp32 0x7f7fffff 0x7f7fffff).flags .invalid = true := by decide +kernel

private def cancel32 : List fp32.Word := [0x4c000000,0x3f800000,0xcc000000]
private def cancel64 : List fp64.Word := [0x4350000000000000,0x3ff0000000000000,0xc350000000000000]

example : (compensatedSum? fp32 cancel32).map (fun r => (r.result.value,r.errorBound)) =
    some (0x3f800000#32,0) ∧
    (compensatedSum? fp64 cancel64).map (fun r => (r.result.value,r.errorBound)) =
      some (0x3ff0000000000000#64,0) ∧
    (compensatedSum? fp32 cancel32).map (fun r => compensationFlags r.result) =
      some [false,false,false,false,true] := by decide +kernel

/-- The correction accumulator itself can round: the certificate includes that loss. -/
example : (compensatedSum? fp32 [0x4c000000,0x3f800000,0x33800000,0xcc000000]).map
      (fun r => (r.result.value,r.errorBound,r.state.radius)) =
    some (0x3f800000#32,(2 : ℚ)^(-24 : ℤ),(2 : ℚ)^(-24 : ℤ)) := by decide +kernel

/-- Final rounding is accounted for even when all correction additions were exact. -/
example : (compensatedSum? fp32 [0x3f800000,0x33800000]).map
      (fun r => (r.result.value,r.errorBound,r.state.radius)) =
    some (0x3f800000#32,(2 : ℚ)^(-24 : ℤ),0) ∧
    (compensatedSum? fp64 []).map (fun r => (r.result.value,r.errorBound)) = some (0#64,0) ∧
    (compensatedSum? fp32 [1,1,1]).map (fun r => (r.result.value,r.errorBound)) = some (3#32,0) ∧
    (compensatedSum? fp32 [0x7f7fffff,0x7f7fffff]).isNone = true ∧
    (compensatedSum? fp32 [0x7f800000]).isNone = true := by decide +kernel

/-- A complete proof about the total IEEE result, obtained from a computed certificate. -/
example : fp32.decode? (compensatedSum fp32 cancel32).value = some 1 := by
  have h := compensatedSum_exact_of_zero_bound fp32 cancel32 (by decide +kernel)
  have hs : wordListSum fp32 cancel32 = 1 := by decide +kernel
  simpa [hs] using h

example : fp64.decode? (compensatedSum fp64 cancel64).value = some 1 := by
  have h := compensatedSum_exact_of_zero_bound fp64 cancel64 (by decide +kernel)
  have hs : wordListSum fp64 cancel64 = 1 := by decide +kernel
  simpa [hs] using h

/-- The exact sum remains enclosed when the correction addition is inexact. -/
example : compensatedEnclosure? fp32 [0x4c000000,0x3f800000,0x33800000,0xcc000000] =
    some ⟨1-(2 : ℚ)^(-24 : ℤ),1+(2 : ℚ)^(-24 : ℤ)⟩ := by decide +kernel

example : (compensatedSum fp32 [0x7f7fffff,0x7f7fffff]).flags .overflow = true ∧
    (compensatedSum fp32 [0x7f7fffff,0x7f7fffff]).flags .invalid = true := by decide +kernel
end FP.IEEE.Software.Tests
