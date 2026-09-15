import FP.IEEE.Software.Arithmetic

/-! Kernel regressions for arithmetic class dispatch, signed zeros, payload
selection, numerical boundaries, and sticky composition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace FP.IEEE.Software.Tests

private def modes : List RoundingMode :=
  [.nearestEven, .nearestAway, .towardZero, .towardPositive, .towardNegative]
private def flags (r : Result α) : List Bool :=
  [.invalid, .divideByZero, .overflow, .underflow, .inexact].map r.flags
private def ops : List BinaryOp := [.add, .sub, .mul]

/-- Signaling NaNs take priority, and subtraction preserves the original NaN sign. -/
example : (ops.map fun op => (binary fp32 op .nearestEven 0x7fc00123 0xff800456).value.toNat) =
    List.replicate 3 0xffc00456 ∧
    (ops.map fun op => flags (binary fp32 op .nearestEven 0x7fc00123 0xff800456)) =
    List.replicate 3 [true, false, false, false, false] := by decide +kernel

example : (sub fp64 .nearestEven 0x3ff0000000000000 0xfff8000000000123).value =
    0xfff8000000000123#64 ∧
    flags (sub fp64 .nearestEven 0x3ff0000000000000 0xfff8000000000123) =
    [false, false, false, false, false] := by decide +kernel

example : (mul fp32 .nearestEven 0 0x7fc00123).value = 0x7fc00123#32 ∧
    flags (mul fp32 .nearestEven 0 0x7fc00123) = [false, false, false, false, false] := by decide +kernel

/-- Each operation-specific invalid case delivers the default NaN and only invalid. -/
example : ([add fp32 .nearestEven 0x7f800000 0xff800000,
    sub fp32 .nearestEven 0x7f800000 0x7f800000,
    mul fp32 .nearestEven 0x80000000 0x7f800000].map fun r => r.value.toNat) =
    List.replicate 3 0x7fc00000 ∧
    ([add fp32 .nearestEven 0x7f800000 0xff800000,
    sub fp32 .nearestEven 0x7f800000 0x7f800000,
    mul fp32 .nearestEven 0x80000000 0x7f800000].map flags) =
    List.replicate 3 [true, false, false, false, false] := by decide +kernel

example : (sub fp64 .towardZero 0x7ff0000000000000 0xfff0000000000000).value =
    0x7ff0000000000000#64 ∧
    (mul fp64 .towardPositive 0xfff0000000000000 0xbff0000000000000).value =
    0x7ff0000000000000#64 ∧
    flags (mul fp64 .towardPositive 0xfff0000000000000 0xbff0000000000000) =
    [false, false, false, false, false] := by decide +kernel

/-- Cancellation differs from combining like-signed zeros. -/
example : (modes.map fun m => (sub fp32 m 0x3f800000 0x3f800000).value.toNat) =
    [0, 0, 0, 0, 0x80000000] ∧
    (modes.map fun m => (add fp32 m 0x80000000 0x80000000).value.toNat) =
    List.replicate 5 0x80000000 ∧
    (modes.map fun m => (sub fp32 m 0x80000000 0).value.toNat) =
    List.replicate 5 0x80000000 := by decide +kernel

example : (modes.map fun m => (sub fp64 m 0x8000000000000000 0x8000000000000000).value.toNat) =
    [0, 0, 0, 0, 0x8000000000000000] ∧
    (mul fp64 .towardNegative 0x8000000000000000 0xbff0000000000000).value = 0#64 := by decide +kernel

/-- Actual arithmetic at an ordinary halfway case. -/
example : (modes.map fun m => (add fp32 m 0x3f800000 0x33800000).value.toNat) =
    [0x3f800000, 0x3f800001, 0x3f800000, 0x3f800001, 0x3f800000] := by decide +kernel

/-- Exact and inexact underflow remain distinct. -/
example : (mul fp32 .nearestEven 0x00800000 0x3f000000).value = 0x00400000#32 ∧
    flags (mul fp32 .nearestEven 0x00800000 0x3f000000) = [false, false, false, false, false] ∧
    (mul fp32 .nearestEven 0x80000001 0x3f000000).value = 0x80000000#32 ∧
    flags (mul fp32 .nearestEven 0x80000001 0x3f000000) = [false, false, false, true, true] := by decide +kernel

example : (modes.map fun m => (mul fp64 m 1 0x3fe0000000000000).value.toNat) = [0, 1, 0, 1, 0] ∧
    (modes.map fun m => flags (mul fp64 m 1 0x3fe0000000000000)) =
    List.replicate 5 [false, false, false, true, true] := by decide +kernel

example : (modes.map fun m => (add fp32 m 0x7f7fffff 0x73000000).value.toNat) =
    [0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff] ∧
    flags (add fp32 .towardZero 0x7f7fffff 0x73000000) =
    [false, false, false, false, true] := by decide +kernel

/-- Overflow is retained when a later operation raises invalid. -/
example : flags ((mul fp64 .nearestEven 0x7fefffffffffffff 0x4000000000000000).bind
    (fun w => sub fp64 .nearestEven w w)) = [true, false, true, false, true] := by decide +kernel

end FP.IEEE.Software.Tests
