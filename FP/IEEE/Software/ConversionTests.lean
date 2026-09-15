import FP.IEEE.Software.MixedArithmetic
import FP.IEEE.Software.Widening

/-! Kernel regressions for format conversion and mixed source/destination arithmetic. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests
private def flags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags
private def modes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

/-- High-aligned payloads survive widening followed by narrowing. -/
example : (convert fp32 fp64 .nearestEven 0xffc00123).value = 0xfff8002460000000#64 ∧
    (convert fp64 fp32 .nearestEven (convert fp32 fp64 .nearestEven 0xffc00123).value).value =
      0xffc00123#32 ∧ flags (convert fp32 fp64 .nearestEven 0xffc00123) =
      [false, false, false, false, false] := by decide +kernel

/-- Truncating every payload bit still produces a NaN, and signaling raises invalid only. -/
example : (convert fp64 fp32 .nearestEven 0xfff0000000000001).value = 0xffc00000#32 ∧
    flags (convert fp64 fp32 .nearestEven 0xfff0000000000001) =
      [true, false, false, false, false] := by decide +kernel

example : (convert fp32 fp64 .towardPositive 0x80000000).value = 0x8000000000000000#64 ∧
    (convert fp64 fp32 .towardZero 0xfff0000000000000).value = 0xff800000#32 ∧
    flags (convert fp64 fp32 .towardZero 0xfff0000000000000) =
      [false, false, false, false, false] := by decide +kernel

/-- Exact widening includes subnormals and maxFinite. -/
example : (convert fp32 fp64 .nearestEven 1).value = 0x36a0000000000000#64 ∧
    (convert fp32 fp64 .nearestEven 0x7f7fffff).value = 0x47efffffe0000000#64 ∧
    flags (convert fp32 fp64 .towardNegative 1) = [false, false, false, false, false] := by decide +kernel

/-- Narrowing is one rounding in the chosen direction. -/
example : (modes.map fun m => (convert fp64 fp32 m 0x3ff0000010000000).value.toNat) =
    [0x3f800000, 0x3f800001, 0x3f800000, 0x3f800001, 0x3f800000] ∧
    (modes.map fun m => (convert fp64 fp32 m 0x3690000000000000).value.toNat) =
    [0, 1, 0, 1, 0] := by decide +kernel

example : flags (convert fp64 fp32 .nearestEven 0x3690000000000000) =
    [false, false, false, true, true] ∧
    (convert fp64 fp32 .towardZero 0x7fefffffffffffff).value = 0x7f7fffff#32 ∧
    flags (convert fp64 fp32 .towardZero 0x7fefffffffffffff) =
    [false, false, true, false, true] := by decide +kernel

/-- Early operand conversion would erase the exact cancellation residual. -/
example : (mixedAdd fp64 fp32 fp32 .nearestEven 0x3ff0000000400000 0xbf800000).value =
    0x30800000#32 ∧
    flags (mixedAdd fp64 fp32 fp32 .nearestEven 0x3ff0000000400000 0xbf800000) =
      [false, false, false, false, false] ∧
    (add fp32 .nearestEven (convert fp64 fp32 .nearestEven 0x3ff0000000400000).value
      0xbf800000).value = 0#32 := by decide +kernel

/-- Mixed NaN priority is decided before payload conversion or subtraction sign changes. -/
example : (mixedSub fp32 fp64 fp32 .nearestEven 0x7fc00456 0xfff0002460000000).value =
    0xffc00123#32 ∧
    flags (mixedSub fp32 fp64 fp32 .nearestEven 0x7fc00456 0xfff0002460000000) =
    [true, false, false, false, false] := by decide +kernel

example : (mixedMul fp32 fp64 fp64 .nearestEven 0 0x7ff0000000000000).value =
    0x7ff8000000000000#64 ∧
    flags (mixedMul fp32 fp64 fp64 .nearestEven 0 0x7ff0000000000000) =
    [true, false, false, false, false] := by decide +kernel

/-- Both mixed directions and both destination widths. -/
example : (mixedMul fp32 fp64 fp64 .nearestEven 0x3f000000 0x4000000000000000).value =
    0x3ff0000000000000#64 ∧
    (mixedMul fp64 fp32 fp32 .nearestEven 0x3fe0000000000000 0x40000000).value =
    0x3f800000#32 ∧
    (mixedAdd fp32 fp32 fp64 .nearestEven 0x3f800000 0x33800000).value =
    0x3ff0000010000000#64 ∧
    (mixedSub fp64 fp64 fp32 .towardNegative 0x3ff0000000000000 0x3ff0000000000000).value =
    0x80000000#32 := by decide +kernel

end FP.IEEE.Software.Tests
