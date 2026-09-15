import FP.IEEE.Software.Division

/-! Kernel regressions for total same-format and mixed-format division. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests
private def flags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags
private def modes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

/-- Finite nonzero / signed zero: signed infinity, only divideByZero. -/
example : (div fp32 .nearestEven 0x3f800000 0x80000000).value = 0xff800000#32 ∧
    flags (div fp32 .nearestEven 0x3f800000 0x80000000) = [false, true, false, false, false] ∧
    (div fp64 .towardZero 0xbff0000000000000 0x8000000000000000).value =
      0x7ff0000000000000#64 := by decide +kernel

/-- Infinity / zero is not an operation on two finite operands. -/
example : (div fp64 .towardNegative 0x7ff0000000000000 0x8000000000000000).value =
    0xfff0000000000000#64 ∧
    flags (div fp64 .towardNegative 0x7ff0000000000000 0x8000000000000000) =
      [false, false, false, false, false] := by decide +kernel

example : (div fp32 .nearestEven 0 0x80000000).value = 0x7fc00000#32 ∧
    flags (div fp32 .nearestEven 0 0x80000000) = [true, false, false, false, false] ∧
    (div fp64 .nearestEven 0x7ff0000000000000 0xfff0000000000000).value =
      0x7ff8000000000000#64 ∧
    flags (div fp64 .nearestEven 0x7ff0000000000000 0xfff0000000000000) =
      [true, false, false, false, false] := by decide +kernel

/-- Exact zero and infinity signs use XOR, independently of rounding direction. -/
example : (modes.map fun m => (div fp32 m 0x80000000 0x40400000).value.toNat) =
    List.replicate 5 0x80000000 ∧
    (div fp64 .nearestEven 0x3ff0000000000000 0xfff0000000000000).value = 0x8000000000000000#64 ∧
    flags (div fp64 .nearestEven 0x3ff0000000000000 0xfff0000000000000) =
      [false, false, false, false, false] := by decide +kernel

/-- Recurring exact quotients exercise directed rounding in both formats. -/
example : (modes.map fun m => (div fp32 m 0x3f800000 0x40400000).value.toNat) =
    [0x3eaaaaab, 0x3eaaaaab, 0x3eaaaaaa, 0x3eaaaaab, 0x3eaaaaaa] ∧
    (modes.map fun m => (div fp32 m 0xbf800000 0x40400000).value.toNat) =
    [0xbeaaaaab, 0xbeaaaaab, 0xbeaaaaaa, 0xbeaaaaaa, 0xbeaaaaab] := by decide +kernel

example : (modes.map fun m => (div fp64 m 0x3ff0000000000000 0x4008000000000000).value.toNat) =
    [0x3fd5555555555555, 0x3fd5555555555555, 0x3fd5555555555555,
      0x3fd5555555555556, 0x3fd5555555555555] ∧
    flags (div fp64 .nearestEven 0x3ff0000000000000 0x4008000000000000) =
      [false, false, false, false, true] := by decide +kernel

/-- Subnormal exactness is distinct from flagged underflow. -/
example : (div fp32 .nearestEven 0x00800000 0x40000000).value = 0x00400000#32 ∧
    flags (div fp32 .nearestEven 0x00800000 0x40000000) = [false, false, false, false, false] ∧
    (modes.map fun m => (div fp64 m 1 0x4000000000000000).value.toNat) = [0, 1, 0, 1, 0] ∧
    flags (div fp64 .nearestEven 1 0x4000000000000000) = [false, false, false, true, true] := by decide +kernel

example : (modes.map fun m => (div fp32 m 0x7f7fffff 0x3f000000).value.toNat) =
    [0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff] ∧
    flags (div fp32 .towardZero 0x7f7fffff 0x3f000000) = [false, false, true, false, true] := by decide +kernel

/-- NaN handling precedes zero-divisor dispatch and cross-format conversion. -/
example : (div fp32 .nearestEven 0x7fc00123 0).value = 0x7fc00123#32 ∧
    flags (div fp32 .nearestEven 0x7fc00123 0) = [false, false, false, false, false] ∧
    (mixedDiv fp32 fp64 fp32 .nearestEven 0x7fc00456 0xfff0002460000000).value = 0xffc00123#32 ∧
    flags (mixedDiv fp32 fp64 fp32 .nearestEven 0x7fc00456 0xfff0002460000000) =
      [true, false, false, false, false] := by decide +kernel

/-- Early divisor conversion would spuriously turn a nonzero divisor into zero. -/
example : (mixedDiv fp32 fp64 fp32 .nearestEven 1 0x3690000000000000).value = 0x40000000#32 ∧
    flags (mixedDiv fp32 fp64 fp32 .nearestEven 1 0x3690000000000000) =
      [false, false, false, false, false] ∧
    flags (div fp32 .nearestEven 1 (convert fp64 fp32 .nearestEven 0x3690000000000000).value) =
      [false, true, false, false, false] := by decide +kernel

example : (mixedDiv fp64 fp32 fp64 .nearestEven 0x4008000000000000 0x40000000).value =
    0x3ff8000000000000#64 ∧
    (mixedDiv fp32 fp32 fp64 .nearestEven 0x40400000 0x40000000).value =
    0x3ff8000000000000#64 ∧
    (mixedDiv fp64 fp64 fp32 .nearestEven 0x4008000000000000 0x4000000000000000).value =
    0x3fc00000#32 := by decide +kernel

/-- A later invalid operation does not erase an earlier divideByZero flag. -/
example : flags ((div fp32 .nearestEven 0x3f800000 0).bind
    (fun w => sub fp32 .nearestEven w w)) = [true, true, false, false, false] := by decide +kernel

end FP.IEEE.Software.Tests
