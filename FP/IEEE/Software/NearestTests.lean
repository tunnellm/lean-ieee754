import FP.IEEE.Software.Nearest

/-! Kernel-checked encoding and exception boundaries for total nearest-even rounding. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace FP.IEEE.Software.Tests
open Interchange

private def flags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags

theorem encode_one32 : encodeFinite? fp32 1 = some 0x3f800000#32 := by decide +kernel

theorem encode_one64 : encodeFinite? fp64 1 = some 0x3ff0000000000000#64 := by decide +kernel

theorem signed_zeros32 :
    (roundNearest fp32 0 false).value = 0#32 ∧
    (roundNearest fp32 0 true).value = 0x80000000#32 ∧
    flags (roundNearest fp32 0 true) = [false,false,false,false,false] := by decide +kernel

theorem signed_zeros64 :
    (roundNearest fp64 0 false).value = 0#64 ∧
    (roundNearest fp64 0 true).value = 0x8000000000000000#64 ∧
    flags (roundNearest fp64 0 true) = [false,false,false,false,false] := by decide +kernel

theorem exact_subnormal32 :
    (roundNearest fp32 ((2 : ℚ)^(-149 : ℤ))).value = 1#32 ∧
    flags (roundNearest fp32 ((2 : ℚ)^(-149 : ℤ))) = [false,false,false,false,false] := by
  decide +kernel

theorem exact_subnormal64 :
    (roundNearest fp64 ((2 : ℚ)^(-1074 : ℤ))).value = 1#64 ∧
    flags (roundNearest fp64 ((2 : ℚ)^(-1074 : ℤ))) = [false,false,false,false,false] := by
  decide +kernel

theorem halfway_underflow32 :
    (roundNearest fp32 ((2 : ℚ)^(-150 : ℤ))).value = 0#32 ∧
    (roundNearest fp32 (-(2 : ℚ)^(-150 : ℤ))).value = 0x80000000#32 ∧
    flags (roundNearest fp32 ((2 : ℚ)^(-150 : ℤ))) = [false,false,false,true,true] := by
  decide +kernel

theorem halfway_underflow64 :
    (roundNearest fp64 ((2 : ℚ)^(-1075 : ℤ))).value = 0#64 ∧
    (roundNearest fp64 (-(2 : ℚ)^(-1075 : ℤ))).value = 0x8000000000000000#64 ∧
    flags (roundNearest fp64 ((2 : ℚ)^(-1075 : ℤ))) = [false,false,false,true,true] := by
  decide +kernel

theorem overflow_words32 :
    (roundNearest fp32 (overflowThreshold binary32)).value = 0x7f800000#32 ∧
    (roundNearest fp32 (-overflowThreshold binary32)).value = 0xff800000#32 ∧
    flags (roundNearest fp32 (overflowThreshold binary32)) = [false,false,true,false,true] := by
  decide +kernel

theorem overflow_words64 :
    (roundNearest fp64 (overflowThreshold binary64)).value = 0x7ff0000000000000#64 ∧
    (roundNearest fp64 (-overflowThreshold binary64)).value = 0xfff0000000000000#64 ∧
    flags (roundNearest fp64 (overflowThreshold binary64)) = [false,false,true,false,true] := by
  decide +kernel

/-- After-rounding tininess cannot be determined from the final result class. -/
theorem tiny_rounds_to_normal32 :
    let x := (2 : ℚ)^(-126 : ℤ) - 3/8 * (2 : ℚ)^(-149 : ℤ)
    (roundNearest fp32 x).value = 0x00800000#32 ∧
    flags (roundNearest fp32 x) = [false,false,false,true,true] := by decide +kernel

theorem not_tiny_rounds_to_normal32 :
    let x := (2 : ℚ)^(-126 : ℤ) - 1/4 * (2 : ℚ)^(-149 : ℤ)
    (roundNearest fp32 x).value = 0x00800000#32 ∧
    flags (roundNearest fp32 x) = [false,false,false,false,true] := by decide +kernel

theorem tiny_rounds_to_normal64 :
    let x := (2 : ℚ)^(-1022 : ℤ) - 3/8 * (2 : ℚ)^(-1074 : ℤ)
    (roundNearest fp64 x).value = 0x0010000000000000#64 ∧
    flags (roundNearest fp64 x) = [false,false,false,true,true] := by decide +kernel

end FP.IEEE.Software.Tests
