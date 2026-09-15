import FP.IEEE.Software.Neighbors
import FP.IEEE.Software.Scaling
import FP.IEEE.Software.Intervals
import FP.IEEE.Software.ProductResidual

/-! Kernel regressions and complete numerical certificates for the analysis toolbelt. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace FP.IEEE.Software.Tests
private def toolFlags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags

/-- A binade boundary has different upward and downward spacings. -/
example : (nextUp fp32 0x3f800000).value = 0x3f800001#32 ∧
    (nextDown fp32 0x3f800000).value = 0x3f7fffff#32 ∧
    (nextUp fp64 0xbff0000000000000).value = 0xbfefffffffffffff#64 ∧
    (nextDown fp64 0xbff0000000000000).value = 0xbff0000000000001#64 := by decide +kernel

example : (nextUp fp32 0x80000000).value = 1#32 ∧ (nextDown fp32 0).value = 0x80000001#32 ∧
    (nextUp fp64 0x8000000000000001).value = 0x8000000000000000#64 ∧
    (nextDown fp64 1).value = 0#64 ∧
    (nextUp fp32 0x007fffff).value = 0x00800000#32 ∧
    (nextDown fp32 0x00800000).value = 0x007fffff#32 := by decide +kernel

example : (nextUp fp32 0x7f7fffff).value = 0x7f800000#32 ∧
    toolFlags (nextUp fp32 0x7f7fffff) = [false, false, false, false, false] ∧
    (nextDown fp64 0xffefffffffffffff).value = 0xfff0000000000000#64 ∧
    toolFlags (nextDown fp64 0xffefffffffffffff) = [false, false, false, false, false] ∧
    (nextUp fp64 0xfff0000000000000).value = 0xffefffffffffffff#64 ∧
    (nextDown fp32 0x7f800000).value = 0x7f7fffff#32 ∧
    (nextUp fp32 0x7f800000).value = 0x7f800000#32 := by decide +kernel

example : (nextUp fp32 0xff800123).value = 0xffc00123#32 ∧
    toolFlags (nextUp fp32 0xff800123) = [true, false, false, false, false] ∧
    (nextDown fp64 0xfff8000000000456).value = 0xfff8000000000456#64 ∧
    toolFlags (nextDown fp64 0xfff8000000000456) = [false, false, false, false, false] := by decide +kernel

example : (scaleB fp32 .nearestEven 0x3fc00000 3).value = 0x41400000#32 ∧
    toolFlags (scaleB fp32 .nearestEven 0x3fc00000 3) = [false, false, false, false, false] ∧
    (scaleB fp64 .towardNegative 0x8000000000000000 500).value = 0x8000000000000000#64 ∧
    (scaleB fp32 .nearestEven 0x00800000 (-1)).value = 0x00400000#32 ∧
    toolFlags (scaleB fp32 .nearestEven 0x00800000 (-1)) = [false, false, false, false, false] := by decide +kernel

example : exactScale? fp32 .nearestEven 1 (-1) = none ∧
    (scaleB fp32 .towardPositive 1 (-1)).value = 1#32 ∧
    toolFlags (scaleB fp32 .nearestEven 1 (-1)) = [false, false, false, true, true] ∧
    exactScale? fp64 .nearestEven 0x7fefffffffffffff 1 = none ∧
    (scaleB fp64 .towardZero 0x7fefffffffffffff 1).value = 0x7fefffffffffffff#64 := by decide +kernel

example : normalizeWord? fp32 1 = some (0x3f800000#32, -149) ∧
    normalizeWord? fp64 1 = some (0x3ff0000000000000#64, -1074) ∧
    normalizeWord? fp64 0xffefffffffffffff = some (0xbfffffffffffffff#64, 1023) ∧
    normalizeWord? fp32 0x80000000 = none ∧ finiteExponent? fp32 0x7f800000 = none := by decide +kernel

example : (enclose fp32 ⟨1/3,1/3⟩).map (fun r => r.value) = some (0x3eaaaaaa#32,0x3eaaaaab#32) ∧
    (enclose fp64 ⟨1/3,1/3⟩).map (fun r => r.value) =
      some (0x3fd5555555555555#64,0x3fd5555555555556#64) := by decide +kernel

example : (intervalAdd fp32 (0x3f800000,0x3f800000) (0x33800000,0x33800000)).map (fun r => r.value) =
    some (0x3f800000#32,0x3f800001#32) ∧
    (intervalMul fp32 (0xc0000000,0x40400000) (0xc0800000,0x40a00000)).map (fun r => r.value) =
      some (0xc1400000#32,0x41700000#32) := by decide +kernel

example : intervalOfWords? fp32 (0x40000000,0x3f800000) = none ∧
    intervalOfWords? fp32 (0,0x7f800000) = none ∧
    (enclose fp32 ⟨(2 : ℚ)^(128 : ℤ),(2 : ℚ)^(128 : ℤ)⟩).isNone = true := by decide +kernel

/-- A complete certificate proves an enclosure of the mathematical value 1/3. -/
example : WordContains fp32 (0x3eaaaaaa,0x3eaaaaab) ((1 : ℝ)/3) := by
  exact enclose_value_sound fp32 ⟨1/3,1/3⟩ _ (by decide +kernel) _
    (by norm_num [FP.Range.Interval.Contains])

/-- The high multiplication is inexact, but its FMA residual recovers the exact product. -/
example : (certifiedTwoProduct? fp32 0x3f800001 0x3f7ffffe).map (fun r => r.value) =
    some (0x3f800000#32,0xa8800000#32) ∧
    (certifiedTwoProduct? fp32 0x3f800001 0x3f7ffffe).map toolFlags =
      some [false, false, false, false, true] ∧
    (certifiedTwoProduct? fp32 1 0x3f000000).isNone = true ∧
    (certifiedTwoProduct? fp64 0x7fefffffffffffff 0x4000000000000000).isNone = true := by decide +kernel

example : (enclose fp32 ⟨2,1⟩).isNone = true ∧
    (enclose fp32 ⟨(2 : ℚ)^(-151 : ℤ),(2 : ℚ)^(-151 : ℤ)⟩).map (fun r => r.value) =
      some (0#32,1#32) ∧
    exactScale? fp32 .nearestEven 0x7fc00123 0 = none ∧
    exactScale? fp32 .nearestEven 0x7f800000 0 = none := by decide +kernel
end FP.IEEE.Software.Tests
