import FP.IEEE.Software.Sqrt

/-! Kernel checks for irrational rounding, signed specials and mixed-format range events. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests
private def sqrtFlagsList (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags
private def sqrtModes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

example : (sqrtModes.map fun m => (sqrt fp32 m 0x40000000).value.toNat) =
    [0x3fb504f3, 0x3fb504f3, 0x3fb504f3, 0x3fb504f4, 0x3fb504f3] ∧
    sqrtFlagsList (sqrt fp32 .nearestEven 0x40000000) = [false, false, false, false, true] := by
  decide +kernel

example : (sqrtModes.map fun m => (sqrt fp64 m 0x4000000000000000).value.toNat) =
    [0x3ff6a09e667f3bcd, 0x3ff6a09e667f3bcd, 0x3ff6a09e667f3bcc, 0x3ff6a09e667f3bcd, 0x3ff6a09e667f3bcc] ∧
    sqrtFlagsList (sqrt fp64 .nearestEven 0x4000000000000000) = [false, false, false, false, true] := by
  decide +kernel

example : (sqrtModes.map fun m => (sqrt fp32 m 0x80000000).value.toNat) = List.replicate 5 0x80000000 ∧
    (sqrt fp64 .nearestEven 0x8000000000000000).value = 0x8000000000000000#64 ∧
    sqrtFlagsList (sqrt fp64 .nearestEven 0x8000000000000000) = [false, false, false, false, false] ∧
    (sqrt fp32 .towardNegative 0).value = 0#32 := by decide +kernel

example : (sqrt fp64 .nearestEven 0x7ff0000000000000).value = 0x7ff0000000000000#64 ∧
    sqrtFlagsList (sqrt fp64 .nearestEven 0x7ff0000000000000) = [false, false, false, false, false] ∧
    (sqrt fp32 .nearestEven 0xff800000).value = 0x7fc00000#32 ∧
    sqrtFlagsList (sqrt fp32 .nearestEven 0xff800000) = [true, false, false, false, false] ∧
    sqrtFlagsList (sqrt fp64 .nearestEven 0xbff0000000000000) = [true, false, false, false, false] := by
  decide +kernel

example : (sqrt fp32 .nearestEven 0xffc00123).value = 0xffc00123#32 ∧
    sqrtFlagsList (sqrt fp32 .nearestEven 0xffc00123) = [false, false, false, false, false] ∧
    (mixedSqrt fp64 fp32 .nearestEven 0xfff0002460000000).value = 0xffc00123#32 ∧
    sqrtFlagsList (mixedSqrt fp64 fp32 .nearestEven 0xfff0002460000000) =
      [true, false, false, false, false] := by decide +kernel

/-- Extreme subnormal inputs can have exact, normal square roots. -/
example : (sqrt fp64 .nearestEven 1).value = 0x1e60000000000000#64 ∧
    sqrtFlagsList (sqrt fp64 .nearestEven 1) = [false, false, false, false, false] ∧
    (sqrt fp32 .nearestEven 0x00800000).value = 0x20000000#32 ∧
    sqrtFlagsList (sqrt fp32 .nearestEven 0x00800000) = [false, false, false, false, false] := by
  decide +kernel

/-- Mixed-format range handling occurs after square root, not before it. -/
example : (sqrtModes.map fun m => (mixedSqrt fp64 fp32 m 0x4ff0000000000000).value.toNat) =
    [0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff] ∧
    sqrtFlagsList (mixedSqrt fp64 fp32 .towardZero 0x4ff0000000000000) =
      [false, false, true, false, true] ∧
    (sqrtModes.map fun m => (mixedSqrt fp64 fp32 m 0x2d30000000000000).value.toNat) = [0, 1, 0, 1, 0] ∧
    sqrtFlagsList (mixedSqrt fp64 fp32 .nearestEven 0x2d30000000000000) =
      [false, false, false, true, true] := by decide +kernel

example : (mixedSqrt fp64 fp32 .nearestEven 0x2d50000000000000).value = 1#32 ∧
    sqrtFlagsList (mixedSqrt fp64 fp32 .nearestEven 0x2d50000000000000) =
      [false, false, false, false, false] ∧
    (mixedSqrt fp32 fp64 .nearestEven 0x40800000).value = 0x4000000000000000#64 := by decide +kernel

/-- Squared midpoint comparisons cover both parities and ties away. -/
example : (sqrtModes.map fun m => sqrtRoundInt m (25/4)) = [2, 3, 2, 3, 2] ∧
    (sqrtModes.map fun m => sqrtRoundInt m (49/4)) = [4, 4, 3, 4, 3] := by decide +kernel

/-- Tininess uses unbounded-exponent precision rounding, not the final word class. -/
example :
    (roundSqrt fp32 .nearestEven (((2 : ℚ)^(-126 : ℤ) - (2 : ℚ)^(-150 : ℤ))^2)
      (sq_nonneg _)).value = 0x00800000#32 ∧
    sqrtFlagsList (roundSqrt fp32 .nearestEven (((2 : ℚ)^(-126 : ℤ) - (2 : ℚ)^(-150 : ℤ))^2)
      (sq_nonneg _)) = [false, false, false, true, true] ∧
    (roundSqrt fp32 .nearestEven (((2 : ℚ)^(-126 : ℤ) - (2 : ℚ)^(-151 : ℤ))^2)
      (sq_nonneg _)).value = 0x00800000#32 ∧
    sqrtFlagsList (roundSqrt fp32 .nearestEven (((2 : ℚ)^(-126 : ℤ) - (2 : ℚ)^(-151 : ℤ))^2)
      (sq_nonneg _)) = [false, false, false, false, true] := by decide +kernel
end FP.IEEE.Software.Tests
