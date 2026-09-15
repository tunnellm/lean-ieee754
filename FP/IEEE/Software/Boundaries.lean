import FP.IEEE.Software.Sign
import FP.IEEE.Software.NaN
import FP.IEEE.Software.ScaledRound
import FP.Native.Subtraction
import FP.Native.Residuals

/-! Kernel-checked regression cases for the total representation, quiet
operations, explicit state, and executable rational rounding foundations. -/
set_option backward.isDefEq.respectTransparency false

namespace FP.IEEE.Software.Tests
open Interchange

private def classes32 : List (Nat × Datum.Class) :=
  [(0x7f800001, .signalingNaN), (0x7fc12345, .quietNaN),
   (0xff800000, .negativeInfinity), (0xbf800000, .negativeNormal),
   (0x80000001, .negativeSubnormal), (0x80000000, .negativeZero),
   (0, .positiveZero), (1, .positiveSubnormal),
   (0x3f800000, .positiveNormal), (0x7f800000, .positiveInfinity)]

private def classes64 : List (Nat × Datum.Class) :=
  [(0x7ff0000000000001, .signalingNaN), (0x7ff8123456789abc, .quietNaN),
   (0xfff0000000000000, .negativeInfinity), (0xbff0000000000000, .negativeNormal),
   (0x8000000000000001, .negativeSubnormal), (0x8000000000000000, .negativeZero),
   (0, .positiveZero), (1, .positiveSubnormal),
   (0x3ff0000000000000, .positiveNormal), (0x7ff0000000000000, .positiveInfinity)]

theorem classification32 : classes32.all
    (fun (bits, tag) => decide (classify fp32 (BitVec.ofNat 32 bits) = tag)) = true := by
  decide +kernel

theorem classification64 : classes64.all
    (fun (bits, tag) => decide (classify fp64 (BitVec.ofNat 64 bits) = tag)) = true := by
  decide +kernel

theorem signed_nan_negation32 :
    (negate fp32 0x7f812345#32).value = 0xff812345#32 ∧
    (abs fp32 0xff812345#32).value = 0x7f812345#32 ∧
    (copySign fp32 0x7fc12345#32 0x80000000#32).value = 0xffc12345#32 := by
  decide +kernel

theorem signed_nan_negation64 :
    (negate fp64 0x7ff0123456789abc#64).value = 0xfff0123456789abc#64 ∧
    (abs fp64 0xfff0123456789abc#64).value = 0x7ff0123456789abc#64 := by
  decide +kernel

theorem zero_numeric_equality :
    (compare fp32 fp32 .quiet Relation.eq 0#32 0x80000000#32).value = true ∧
    (compare fp64 fp64 .quiet Relation.eq 0#64 0x8000000000000000#64).value = true := by
  decide +kernel

theorem unordered_nan_comparisons :
    (compare fp32 fp32 .quiet Relation.eq 0x7fc00001#32 0x7fc00001#32).value = false ∧
    (compare fp32 fp32 .quiet Relation.ne 0x7fc00001#32 0x7fc00001#32).value = true ∧
    (compare fp32 fp32 .quiet Relation.eq 0x7fc00001#32 0#32).flags .invalid = false ∧
    (compare fp32 fp32 .signaling Relation.eq 0x7fc00001#32 0#32).flags .invalid = true ∧
    (compare fp32 fp32 .quiet Relation.eq 0x7f800001#32 0#32).flags .invalid = true := by
  decide +kernel

theorem infinity_comparisons :
    (compare fp32 fp64 .quiet Relation.lt 0xff800000#32 0xffefffffffffffff#64).value = true ∧
    (compare fp32 fp64 .quiet Relation.eq 0x7f800000#32 0x7ff0000000000000#64).value = true ∧
    (compare fp32 fp64 .quiet Relation.lt 0x7f7fffff#32 0x7ff0000000000000#64).value = true := by
  decide +kernel

theorem signaling_nan_priority :
    let xs := [Datum.decode fp32 0x7fc00007#32,
      Datum.decode fp32 0xff800003#32, Datum.decode fp32 0x7f800005#32]
    (propagateNaN fp32 xs).value.encode = 0xffc00003#32 ∧
    (propagateNaN fp32 xs).flags .invalid = true := by
  decide +kernel

theorem quiet_nan_priority64 :
    let xs := [Datum.decode fp64 0x3ff0000000000000#64,
      Datum.decode fp64 0xfff8123456789abc#64, Datum.decode fp64 0x7ff8000000000001#64]
    (propagateNaN fp64 xs).value.encode = 0xfff8123456789abc#64 ∧
    (propagateNaN fp64 xs).flags .invalid = false := by
  decide +kernel

theorem signed_halfway_rounding :
    roundInt .nearestEven (5/2) = 2 ∧ roundInt .nearestAway (5/2) = 3 ∧
    roundInt .nearestEven (-5/2) = -2 ∧ roundInt .nearestAway (-5/2) = -3 ∧
    roundInt .towardPositive (-5/2) = -2 ∧ roundInt .towardNegative (-5/2) = -3 ∧
    roundInt .towardZero (-5/2) = -2 := by
  decide +kernel

theorem underflow_midpoints32 :
    roundNearest? binary32 ((2 : ℚ) ^ (-150 : ℤ)) = some 0 ∧
    roundNearest? binary32 (3 * (2 : ℚ) ^ (-150 : ℤ)) = some ((2 : ℚ) ^ (-148 : ℤ)) ∧
    scaledRound binary32 .nearestAway ((2 : ℚ) ^ (-150 : ℤ)) = (2 : ℚ) ^ (-149 : ℤ) ∧
    scaledRound binary32 .towardNegative (-(2 : ℚ) ^ (-150 : ℤ)) = -(2 : ℚ) ^ (-149 : ℤ) := by
  decide +kernel

theorem underflow_midpoints64 :
    roundNearest? binary64 ((2 : ℚ) ^ (-1075 : ℤ)) = some 0 ∧
    roundNearest? binary64 (3 * (2 : ℚ) ^ (-1075 : ℤ)) = some ((2 : ℚ) ^ (-1073 : ℤ)) := by
  decide +kernel

theorem overflow_boundary32 :
    roundNearest? binary32 (overflowThreshold binary32) = none ∧
    roundNearest? binary32 (-overflowThreshold binary32) = none ∧
    roundNearest? binary32 ((2 : ℚ)^128 - (2 : ℚ)^104) =
      some ((2 : ℚ)^128 - (2 : ℚ)^104) := by
  decide +kernel

theorem overflow_boundary64 :
    roundNearest? binary64 (overflowThreshold binary64) = none ∧
    roundNearest? binary64 (-overflowThreshold binary64) = none ∧
    roundNearest? binary64 ((2 : ℚ)^1024 - (2 : ℚ)^971) =
      some ((2 : ℚ)^1024 - (2 : ℚ)^971) := by
  decide +kernel

theorem sticky_save_restore :
    let initial : Env := ⟨.towardNegative, Flags.singleton .inexact⟩
    let saved := initial.saveAllFlags
    let raised := initial.raiseFlags (Flags.singleton .invalid)
    let cleared := raised.lowerFlags (Flags.singleton .inexact)
    let restored := cleared.restoreFlags saved (Flags.singleton .inexact)
    restored.flags .invalid = true ∧ restored.flags .inexact = true ∧
    restored.flags .overflow = false ∧ restored.mode = .towardNegative := by
  decide +kernel

/-- Exhaustive execution on a six-bit format: one sign, three exponent, two fraction bits. -/
private def toy : Interchange :=
  ⟨⟨2, -2, 3, by decide⟩, 3, 3, by decide, by decide⟩

private instance : toy.Valid := ⟨by decide, by decide⟩

theorem toy_roundtrip_all : (List.range 64).all
    (fun n => decide ((Datum.decode toy (BitVec.ofNat 6 n)).encode = BitVec.ofNat 6 n)) = true := by
  decide +kernel

theorem toy_finite_count : ((List.range 64).filter
    (fun n => isFinite toy (BitVec.ofNat 6 n))).length = 56 := by
  decide +kernel

end FP.IEEE.Software.Tests
