import FP.IEEE.Software.FMA

/-! Kernel regressions distinguishing fused arithmetic from separate operations. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests
private def fmaFlags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags
private def fmaModes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

/-- The exact residual is -2^-46; rounding the product early loses it. -/
example : (fma fp32 .nearestEven 0x3f800001 0x3f7ffffe 0xbf800000).value = 0xa8800000#32 ∧
    fmaFlags (fma fp32 .nearestEven 0x3f800001 0x3f7ffffe 0xbf800000) =
      [false, false, false, false, false] ∧
    (add fp32 .nearestEven (mul fp32 .nearestEven 0x3f800001 0x3f7ffffe).value 0xbf800000).value = 0#32 := by
  decide +kernel

/-- An unrepresentable intermediate product does not cause fused overflow. -/
example : (fma fp32 .nearestEven 0x7f7fffff 0x40000000 0xff7fffff).value = 0x7f7fffff#32 ∧
    fmaFlags (fma fp32 .nearestEven 0x7f7fffff 0x40000000 0xff7fffff) =
      [false, false, false, false, false] ∧
    (fma fp64 .nearestEven 0x7fefffffffffffff 0x4000000000000000 0xffefffffffffffff).value =
      0x7fefffffffffffff#64 := by decide +kernel

/-- The selected binding raises invalid even with a quiet-NaN third operand. -/
example : (fma fp32 .nearestEven 0 0x7f800000 0xffc00123).value = 0xffc00123#32 ∧
    fmaFlags (fma fp32 .nearestEven 0 0x7f800000 0xffc00123) =
      [true, false, false, false, false] ∧
    (fma fp64 .nearestEven 0x7ff0000000000000 0x3ff0000000000000 0xfff0000000000000).value =
      0x7ff8000000000000#64 := by decide +kernel

example : (mixedFma fp32 fp64 fp32 fp32 .nearestEven 0x7fc00456 0xfff0002460000000 0x7f800789).value =
      0xffc00123#32 ∧
    fmaFlags (mixedFma fp32 fp64 fp32 fp32 .nearestEven 0x7fc00456 0xfff0002460000000 0x7f800789) =
      [true, false, false, false, false] := by decide +kernel

example : (fmaModes.map fun m => (fma fp32 m 0x3f800000 0x3f800000 0xbf800000).value.toNat) =
      [0, 0, 0, 0, 0x80000000] ∧
    (fmaModes.map fun m => (fma fp32 m 0x80000000 0x3f800000 0x80000000).value.toNat) =
      List.replicate 5 0x80000000 := by decide +kernel

example : (fmaModes.map fun m => (fma fp32 m 0x3f800000 0x3f800000 0x33800000).value.toNat) =
      [0x3f800000, 0x3f800001, 0x3f800000, 0x3f800001, 0x3f800000] ∧
    fmaFlags (fma fp32 .nearestEven 1 0x3f000000 0) = [false, false, false, true, true] ∧
    (fma fp32 .nearestEven 1 0x3f000000 0).value = 0#32 := by decide +kernel

/-- Combining source values before destination conversion preserves a tiny residual. -/
example : (mixedFma fp64 fp32 fp32 fp32 .nearestEven 0x3ff0000000000001 0x3f800000 0xbf800000).value =
      0x25800000#32 := by decide +kernel
end FP.IEEE.Software.Tests
