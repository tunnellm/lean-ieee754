import FP.IEEE.Software.TotalRound

/-! Kernel-evaluated all-mode regressions. These supplement the universal
refinement theorems and cover mode/sign-dependent range boundaries. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace FP.IEEE.Software.Tests

private def modes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]

private def flags (f : Flags) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map f

/-- Positive and negative overflow delivery in every mode, in the order above. -/
example : (modes.map fun m => (overflowResult fp32 m false).value.toNat) =
    [0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff] ∧
    (modes.map fun m => (overflowResult fp32 m true).value.toNat) =
    [0xff800000, 0xff800000, 0xff7fffff, 0xff7fffff, 0xff800000] := by decide +kernel

example : (modes.map fun m => (overflowResult fp64 m false).value.toNat) =
    [0x7ff0000000000000, 0x7ff0000000000000, 0x7fefffffffffffff,
      0x7ff0000000000000, 0x7fefffffffffffff] ∧
    (modes.map fun m => (overflowResult fp64 m true).value.toNat) =
    [0xfff0000000000000, 0xfff0000000000000, 0xffefffffffffffff,
      0xffefffffffffffff, 0xfff0000000000000] := by decide +kernel

example : (modes.map fun m => flags (overflowResult fp32 m false).flags) =
    List.replicate 5 [false, false, true, false, true] := by decide +kernel

/-- Exceeding maxFinite does not automatically mean overflow: direction matters. -/
example : (modes.map fun m => overflowWithMode binary32 m
    (maxFinite binary32 + (2 : ℚ)^103)) = [true, true, false, true, false] ∧
    (modes.map fun m => overflowWithMode binary32 m
    (-(maxFinite binary32 + (2 : ℚ)^103))) = [true, true, false, false, true] := by decide +kernel

example : (modes.map fun m => overflowWithMode binary64 m
    (maxFinite binary64 + (2 : ℚ)^970)) = [true, true, false, true, false] := by decide +kernel

example : (modes.map fun m => overflowWithMode binary32 m ((2 : ℚ)^128)) =
    List.replicate 5 true := by decide +kernel

/-- Exact tiny inputs set no flags in any mode. -/
example : (modes.map fun m => flags (roundingFlags binary32 m ((2 : ℚ)^(-149 : ℤ)))) =
    List.replicate 5 [false, false, false, false, false] ∧
    (modes.map fun m => flags (roundingFlags binary64 m (-((2 : ℚ)^(-1074 : ℤ))))) =
    List.replicate 5 [false, false, false, false, false] := by decide +kernel

/-- Signed half-subnormal ties distinguish nearest-even, nearest-away and directed modes. -/
example : (modes.map fun m => scaledRound binary32 m ((2 : ℚ)^(-150 : ℤ))) =
    [0, (2 : ℚ)^(-149 : ℤ), 0, (2 : ℚ)^(-149 : ℤ), 0] ∧
    (modes.map fun m => scaledRound binary32 m (-((2 : ℚ)^(-150 : ℤ)))) =
    [0, -((2 : ℚ)^(-149 : ℤ)), 0, 0, -((2 : ℚ)^(-149 : ℤ))] := by decide +kernel

example : (modes.map fun m => flags (roundingFlags binary64 m ((2 : ℚ)^(-1075 : ℤ)))) =
    List.replicate 5 [false, false, false, true, true] := by decide +kernel

/-- After-precision tininess at a boundary depends on the rounding direction. -/
example : (modes.map fun m => tinyWithMode binary32 m
    ((2 : ℚ)^(-126 : ℤ) - (2 : ℚ)^(-151 : ℤ))) =
    [false, false, true, false, true] := by decide +kernel

/-- Full encoder path at ordinary ties and binade carry, for both formats. -/
example : (modes.map fun m => (roundWithMode fp32 m (1 + (2 : ℚ)^(-24 : ℤ))).value.toNat) =
    [0x3f800000, 0x3f800001, 0x3f800000, 0x3f800001, 0x3f800000] ∧
    (modes.map fun m => (roundWithMode fp32 m (2 - (2 : ℚ)^(-24 : ℤ))).value.toNat) =
    [0x40000000, 0x40000000, 0x3fffffff, 0x40000000, 0x3fffffff] := by decide +kernel

example : (modes.map fun m => (roundWithMode fp64 m (-(1 + (2 : ℚ)^(-53 : ℤ)))).value.toNat) =
    [0xbff0000000000000, 0xbff0000000000001, 0xbff0000000000000,
      0xbff0000000000000, 0xbff0000000000001] ∧
    (modes.map fun m => (roundWithMode fp64 m (2 - (2 : ℚ)^(-53 : ℤ))).value.toNat) =
    [0x4000000000000000, 0x4000000000000000, 0x3fffffffffffffff,
      0x4000000000000000, 0x3fffffffffffffff] := by decide +kernel

example : (modes.map fun m => (roundWithMode fp32 m 0 true).value.toNat) =
    List.replicate 5 0x80000000 ∧
    (modes.map fun m => (roundWithMode fp64 m 0 true).value.toNat) =
    List.replicate 5 0x8000000000000000 := by decide +kernel

example : (modes.map fun m => (roundWithMode fp32 m (-((2 : ℚ)^(-150 : ℤ)))).value.toNat) =
    [0x80000000, 0x80000001, 0x80000000, 0x80000000, 0x80000001] ∧
    (modes.map fun m => (roundWithMode fp64 m ((2 : ℚ)^(-1075 : ℤ))).value.toNat) =
    [0, 1, 0, 1, 0] := by decide +kernel

/-- Whole rounder: all modes overflow at the next binade, with correct delivery. -/
example : (modes.map fun m => (roundWithMode fp32 m ((2 : ℚ)^128)).value.toNat) =
    [0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff] ∧
    (modes.map fun m => flags (roundWithMode fp32 m ((2 : ℚ)^128)).flags) =
    List.replicate 5 [false, false, true, false, true] := by decide +kernel

/-- Same rounded maxFinite word can be inexact without overflow. -/
example : (roundWithMode fp64 .towardZero (maxFinite binary64 + (2 : ℚ)^970)).value =
    0x7fefffffffffffff#64 ∧
    flags (roundWithMode fp64 .towardZero (maxFinite binary64 + (2 : ℚ)^970)).flags =
    [false, false, false, false, true] := by decide +kernel

end FP.IEEE.Software.Tests
