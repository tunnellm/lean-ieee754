import FP.IEEE.Software.CompensatedDotList

/-! Online Dot2: kernel checks of words, defects, radii, and exceptional paths. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange
open scoped BigOperators

private def prodCancel32 : List (fp32.Word × fp32.Word) :=
  [(0x3f800001,0x3f7ffffe),(0xbf800000,0x3f800000)]
private def prodCancel64 : List (fp64.Word × fp64.Word) :=
  [(0x3ff0000000000001,0x3feffffffffffffe),(0xbff0000000000000,0x3ff0000000000000)]

/-- Product roundoff is recovered through cancellation, in both formats. -/
example : (compensatedDotList? fp32 prodCancel32).map (fun r => (r.result.value,r.errorBound)) =
    some (0xa8800000#32,0) ∧
    (compensatedDotList? fp64 prodCancel64).map (fun r => (r.result.value,r.errorBound)) =
    some (0xb970000000000000#64,0) := by decide +kernel

/-- End-to-end equality with the mathematical dot product follows from a zero radius. -/
example : fp32.decode? (compensatedDotList fp32 prodCancel32).value = some ((2 : ℝ)^(-46 : ℤ) * (-1)) := by
  have he := compensatedDotList_exact_of_zero_bound fp32 prodCancel32 (by decide +kernel)
  have hs : (prodCancel32.map (fun p => wordRat fp32 p.1*wordRat fp32 p.2)).sum = -(2 : ℚ)^(-46 : ℤ) := by decide +kernel
  simpa [hs] using he

example : fp64.decode? (compensatedDotList fp64 prodCancel64).value = some (-((2 : ℝ)^(-104 : ℤ))) := by
  have he := compensatedDotList_exact_of_zero_bound fp64 prodCancel64 (by decide +kernel)
  have hs : (prodCancel64.map (fun p => wordRat fp64 p.1*wordRat fp64 p.2)).sum = -(2 : ℚ)^(-104 : ℤ) := by decide +kernel
  simpa [hs] using he

/-- The bounded Dot2 certificate succeeds where the exact TwoProduct certificate rejects. -/
example : (certifiedTwoProduct? fp32 1 0x3f000000).isNone = true ∧
    (compensatedDotList? fp32 [(1,0x3f000000)]).map (fun r => (r.result.value,r.state.productDefectMass,r.errorBound)) =
      some (0#32,(2 : ℚ)^(-150 : ℤ),(2 : ℚ)^(-150 : ℤ)) ∧
    (compensatedDotList fp32 [(1,0x3f000000)]).flags .underflow = true ∧
    (compensatedDotList? fp64 [(1,0x3fe0000000000000)]).map (fun r => (r.result.value,r.state.productDefectMass,r.errorBound)) =
      some (0#64,(2 : ℚ)^(-1075 : ℤ),(2 : ℚ)^(-1075 : ℤ)) := by decide +kernel

example : CompensatedDotListFinite fp32 [(1,0x3f000000)] ∧
    CompensatedDotListFinite fp64 [(1,0x3fe0000000000000)] := by decide +kernel

/-- Even the normal-product / tiny-residual case retains its measured defect. -/
example : (compensatedDotList? fp32 [(0x00800001,0x3f800001)]).map
      (fun r => (r.result.value,r.state.productDefectMass,r.errorBound)) =
    some (0x00800002#32,(2 : ℚ)^(-172 : ℤ),(2 : ℚ)^(-172 : ℤ)) := by decide +kernel

/-- Combining the two residuals may round, before correction accumulation. -/
example : (dotStepTrace fp32 0x4c000000 0 0x3f800001 0x3f7ffffe).combined.flags .inexact = true ∧
    (compensatedDotList? fp32 [(0x4c000000,0x3f800000),(0x3f800001,0x3f7ffffe)]).map
      (fun r => (r.result.value,r.state.radius,r.errorBound)) =
      some (0x4c000000#32,(2 : ℚ)^(-46 : ℤ),1+(2 : ℚ)^(-46 : ℤ)) := by decide +kernel

/-- The high-path lost unit is recovered, while a smaller correction can still round. -/
example : (compensatedDotList? fp32 [(0x4c000000,0x3f800000),(0x3f800000,0x3f800000),(0xcc000000,0x3f800000)]).map
      (fun r => (r.result.value,r.errorBound)) = some (0x3f800000#32,0) ∧
    (compensatedDotList? fp32 [(0x4c000000,0x3f800000),(0x3f800000,0x3f800000),
      (0x33800000,0x3f800000),(0xcc000000,0x3f800000)]).map
      (fun r => (r.result.value,r.state.radius,r.errorBound)) =
      some (0x3f800000#32,(2 : ℚ)^(-24 : ℤ),(2 : ℚ)^(-24 : ℤ)) := by decide +kernel

/-- Empty input does not inspect exceptional functions; signed zeros/subnormals are finite. -/
example : (compensatedDot fp32 (fun _ => 0x7fc00123) (fun _ => 0x7f800000) 0).value = 0 ∧
    CompensatedDotListFinite fp32 [(0x80000000,0x3f800000),(1,0x3f800000)] ∧
    CompensatedDotListFinite fp64 [(0x8000000000000000,0x3ff0000000000000),(1,0x3ff0000000000000)] ∧
    (compensatedDotList? fp64 []).map (fun r => (r.result.value,r.errorBound)) = some (0#64,0) := by decide +kernel

/-- Each separate finite-execution qualification excludes an actual failure. -/
example : ¬ CompensatedDotListFinite fp32 [(0x7f7fffff,0x40000000)] ∧
    ¬ CompensatedDotListFinite fp32 [(0x7f7fffff,0x3f800000),(0x7f7fffff,0x3f800000)] ∧
    ¬ CompensatedDotListFinite fp32 [(0xf3c00000,0x3f800000),(0x7f7fffff,0x3f800000)] ∧
    ¬ CompensatedDotStepFinite fp32 0x7f7ffffe 0x7f7fffff 0x73000000 0x3f800000 ∧
    ¬ CompensatedDotListFinite fp32 [(0x7f7fffff,0x3f800000),(0x72800000,0x3f800000),(0x72800000,0x3f800000)] ∧
    (compensatedDotList fp32 [(0x7f7fffff,0x3f800000),(0x72800000,0x3f800000),(0x72800000,0x3f800000)]).flags .overflow = true := by decide +kernel

example : ¬ CompensatedDotListFinite fp64 [(0x7fefffffffffffff,0x4000000000000000)] ∧
    ¬ CompensatedDotListFinite fp64 [(0xfca8000000000000,0x3ff0000000000000),(0x7fefffffffffffff,0x3ff0000000000000)] ∧
    ¬ CompensatedDotStepFinite fp64 0x7feffffffffffffe 0x7fefffffffffffff 0x7c90000000000000 0x3ff0000000000000 ∧
    ¬ CompensatedDotListFinite fp64 [(0x7fefffffffffffff,0x3ff0000000000000),
      (0x7c80000000000000,0x3ff0000000000000),(0x7c80000000000000,0x3ff0000000000000)] ∧
    (compensatedDotList? fp64 [(0x7ff0000000000000,0)]).isNone = true := by decide +kernel

/-- Concrete finiteness alone supplies the general enclosure theorem. -/
example : ∃ J, compensatedDotEnclosure? fp32 (fun _ => 1) (fun _ => 0x3f000000) 1 = some J ∧
    J.Contains (wordDotSum fp32 (fun _ => 1) (fun _ => 0x3f000000) 1 : ℝ) :=
  compensatedDotEnclosure?_exists_of_finite fp32 _ _ 1 (by decide +kernel)

/-- A quantified real-valued interface, with no certificate-success assumption. -/
example (a b : ℕ → fp64.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, fp64.decode? (a i) = some (x i)) (hb : ∀ i < n, fp64.decode? (b i) = some (y i))
    (h : CompensatedDotFinite fp64 a b n) (hn : (2*n : ℕ)*fp64.format.unitRoundoff < 1) :
    ∃ q : ℝ, fp64.decode? (compensatedDot fp64 a b n).value = some q ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ fp64.format.unitRoundoff*|∑ i ∈ Finset.range n, x i*y i|+
        (1+fp64.format.unitRoundoff)*((gamma fp64.format.unitRoundoff (2*n))^2*FP.dotMass x y n+
          3*n*(fp64.format.minSubnormal/2)/(1-(2*n : ℕ)*fp64.format.unitRoundoff)^2)+fp64.format.minSubnormal/2 :=
  compensatedDot_gamma_of_decoded fp64 a b x y n ha hb h hn

example (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : CompensatedDotRange I a b 0 := by
  simp [CompensatedDotRange,CompensatedDotPassRange,compensatedDotCore,Result.pure,
    wordRat,Datum.fields,Fields.rationalValue,I.format.overflowThreshold_pos]

end FP.IEEE.Software.Tests
