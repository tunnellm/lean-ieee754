import FP.IEEE.Software.CompensatedRange

/-! Kernel regressions for compensated-summation completeness and input bounds. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange

private def inputCancel32 : List fp32.Word := [0x4c000000,0x3f800000,0xcc000000]
private def inputCancel64 : List fp64.Word := [0x4350000000000000,0x3ff0000000000000,0xc350000000000000]

/-- Finiteness, rather than a successful certificate, supplies an IEEE error theorem. -/
example : ∃ q : ℝ, fp32.decode? (compensatedSum fp32 inputCancel32).value = some q ∧
    |q-(wordListSum fp32 inputCancel32 : ℝ)| ≤ fp32.format.unitRoundoff*|(wordListSum fp32 inputCancel32 : ℝ)|+
      (1+fp32.format.unitRoundoff)*((growth fp32.format.unitRoundoff inputCancel32.length)^2*
        (wordListAbsSum fp32 inputCancel32 : ℝ)+(fp32.format.minSubnormal/2)*
        (1+growth fp32.format.unitRoundoff inputCancel32.length)*
          geomWeight fp32.format.unitRoundoff inputCancel32.length)+fp32.format.minSubnormal/2 :=
  compensatedSum_mixed_of_finite fp32 inputCancel32 (by decide +kernel)

example : ∃ r, compensatedSum? fp64 inputCancel64 = some r :=
  compensatedSum?_complete fp64 inputCancel64 (by decide +kernel)

/-- These are symbolic theorems for arbitrary inputs, in each interchange format. -/
example (xs : List fp32.Word) (h : CompensatedSumFinite fp32 xs) :
    ∃ r : CompensatedCertificate fp32, compensatedSum? fp32 xs = some r ∧
      compensatedSum fp32 xs = r.result ∧ ∃ q : ℝ,
      fp32.decode? (compensatedSum fp32 xs).value = some q ∧
      |q-(wordListSum fp32 xs : ℝ)| ≤ (r.errorBound : ℝ) :=
  compensatedSum_error_radius_of_finite fp32 xs h

example (xs : List fp64.Word) (ys : List ℝ)
    (hdec : List.Forall₂ (fun w y => fp64.decode? w = some y) xs ys)
    (h : CompensatedSumFinite fp64 xs) (hn : ys.length*fp64.format.unitRoundoff < 1) :
    ∃ q : ℝ, fp64.decode? (compensatedSum fp64 xs).value = some q ∧
      |q-ys.sum| ≤ fp64.format.unitRoundoff*|ys.sum|+
        (1+fp64.format.unitRoundoff)*((gamma fp64.format.unitRoundoff ys.length)^2*(ys.map (fun y => |y|)).sum+
          ys.length*(fp64.format.minSubnormal/2)/(1-ys.length*fp64.format.unitRoundoff)^2)+fp64.format.minSubnormal/2 :=
  compensatedSum_gamma_of_decoded fp64 xs ys hdec h hn

/-- Enclosures remain available without assuming certificate success. -/
example : ∃ J, compensatedEnclosure? fp32 [0x4c000000,0x3f800000,0x33800000,0xcc000000] = some J ∧
    J.Contains (wordListSum fp32 [0x4c000000,0x3f800000,0x33800000,0xcc000000] : ℝ) :=
  compensatedEnclosure?_exists_of_finite fp32 _ (by decide +kernel)

/-- Empty input, signed zeros, and gradual underflow satisfy the finite conditions. -/
example : CompensatedSumFinite fp32 [] ∧ CompensatedSumFinite fp64 [] ∧
    CompensatedSumFinite fp32 [0x80000000,0,1,1,0x80000001] ∧
    CompensatedSumFinite fp64 [0x8000000000000000,0,1,1,0x8000000000000001] := by decide +kernel

/-- Inexact bvirt, correction accumulation, and final rounding are all allowed. -/
example : CompensatedSumFinite fp32 [0xbf800000,0x4c000000] ∧
    CompensatedSumFinite fp64 [0xbff0000000000000,0x4350000000000000] ∧
    CompensatedSumFinite fp32 [0x4c000000,0x3f800000,0x33800000,0xcc000000] ∧
    CompensatedSumFinite fp32 [0x3f800000,0x33800000] := by decide +kernel

/-- A finite pass can still overflow in its final high-plus-correction addition. -/
example : CompensatedPassFinite fp32 0 0 [0x7f7fffff,0x72800000,0x72800000] ∧
    ¬ CompensatedSumFinite fp32 [0x7f7fffff,0x72800000,0x72800000] ∧
    (compensatedSum fp32 [0x7f7fffff,0x72800000,0x72800000]).flags .overflow = true ∧
    CompensatedPassFinite fp64 0 0 [0x7fefffffffffffff,0x7c80000000000000,0x7c80000000000000] ∧
    ¬ CompensatedSumFinite fp64 [0x7fefffffffffffff,0x7c80000000000000,0x7c80000000000000] ∧
    (compensatedSum fp64 [0x7fefffffffffffff,0x7c80000000000000,0x7c80000000000000]).flags .overflow = true := by
  decide +kernel

/-- A valid TwoSum alone does not ensure a finite correction addition. -/
example : (twoSumTrace fp32 0x7f7ffffe 0x73000000).checked = true ∧
    ¬ CompensatedStepFinite fp32 0x7f7ffffe 0x7f7fffff 0x73000000 ∧
    (twoSumTrace fp64 0x7feffffffffffffe 0x7c90000000000000).checked = true ∧
    ¬ CompensatedStepFinite fp64 0x7feffffffffffffe 0x7fefffffffffffff 0x7c90000000000000 := by decide +kernel

/-- The bvirt range qualification also remains necessary inside a summation. -/
example : ¬ CompensatedSumFinite fp32 [0xf3c00000,0x7f7fffff] ∧
    ¬ CompensatedSumFinite fp64 [0xfca8000000000000,0x7fefffffffffffff] ∧
    ¬ CompensatedSumFinite fp32 [0x7f7fffff,0x7f7fffff] ∧
    ¬ CompensatedSumFinite fp64 [0x7fefffffffffffff,0x7fefffffffffffff] ∧
    ¬ CompensatedSumFinite fp32 [0x7f800000] ∧
    ¬ CompensatedSumFinite fp64 [0x7ff8000000000123] := by decide +kernel

/-- The explicit range API also applies at the empty-list boundary. -/
example (I : Interchange) [I.Valid] : CompensatedSumRange I [] := by
  simp [CompensatedSumRange,CompensatedPassRange,compensatedCore,Result.pure,
    wordRat,Datum.isFinite,Datum.fields,Fields.rationalValue,I.format.overflowThreshold_pos]

end FP.IEEE.Software.Tests
