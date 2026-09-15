import FP.IEEE.Software.Cancellation

/-! Kernel regressions across every rounding mode and both interchange formats. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange

private def cancellationModes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

/-- Adjacent normal inputs cancel to the least subnormal, exactly, in all modes. -/
example : cancellationModes.map (fun mode =>
    let r := sub fp32 mode 0x00800001 0x00800000
    (r.value, flagsClear r.flags)) = List.replicate 5 (1#32, true) := by decide +kernel

example : cancellationModes.map (fun mode =>
    let r := sub fp64 mode 0x0010000000000001 0x0010000000000000
    (r.value, flagsClear r.flags)) = List.replicate 5 (1#64, true) := by decide +kernel

/-- Negative operands satisfy the signed-magnitude theorem. -/
example : cancellationModes.map (fun mode =>
    let r := sub fp32 mode 0x80800001 0x80800000
    (r.value, flagsClear r.flags)) = List.replicate 5 (0x80000001#32, true) := by decide +kernel

example : cancellationModes.map (fun mode =>
    let r := sub fp64 mode 0x8010000000000001 0x8010000000000000
    (r.value, flagsClear r.flags)) = List.replicate 5 (0x8000000000000001#64, true) := by decide +kernel

/-- A symbolic all-mode application at the factor-of-two boundary. -/
example (mode : RoundingMode) :
    (Datum.decode fp32 (sub fp32 mode 0x3f800000 0x3f000000).value).toRat? = some (1/2) ∧
    (sub fp32 mode 0x3f800000 0x3f000000).flags = Flags.empty := by
  have h := sub_sterbenz fp32 mode 0x3f800000 0x3f000000 1 (1/2)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Certificate success is derived from input conditions, not executing the checker. -/
example : certifiedTwoSum? fp64 0x3ff0000000000000 0xbfe0000000000000 =
    some (twoSum fp64 0x3ff0000000000000 0xbfe0000000000000) := by
  exact certifiedTwoSum?_of_cancellation fp64 _ _ 1 (-1/2)
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

/-- A halfway addition has a nonzero, representable rounding residual. -/
example : fp32.format.Representable ((1 : ℝ) + (2 : ℝ)^(-24 : ℤ) - 1) := by
  have h := add_residual_representable fp32 0x3f800000 0x33800000 1 ((2 : ℚ)^(-24 : ℤ)) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa using h

end FP.IEEE.Software.Tests
