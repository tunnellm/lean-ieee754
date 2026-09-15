import FP.IEEE.Software.ProductBounds

/-! Kernel boundary regressions for exact and inexact FMA product residuals. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange

/-- At the lattice boundary the residual is exactly the least subnormal. -/
example : TwoProductRange fp32 0x26000001 0x25800001 ∧
    (twoProduct fp32 0x26000001 0x25800001).value = (0x0c000002#32,1#32) ∧
    TwoProductRange fp64 0x21a0000000000001 0x21a0000000000001 ∧
    (twoProduct fp64 0x21a0000000000001 0x21a0000000000001).value = (0x0350000000000002#64,1#64) := by decide +kernel

example : certifiedTwoProduct? fp32 0x26000001 0x25800001 = some (twoProduct fp32 0x26000001 0x25800001) :=
  certifiedTwoProduct?_of_range fp32 _ _ (by decide +kernel)

example : certifiedTwoProduct? fp64 0x21a0000000000001 0x21a0000000000001 =
    some (twoProduct fp64 0x21a0000000000001 0x21a0000000000001) :=
  certifiedTwoProduct?_of_range fp64 _ _ (by decide +kernel)

/-- One exponent step below the boundary loses a half-subnormal residual. -/
example : ¬ TwoProductRange fp32 0x26000001 0x25000001 ∧
    (twoProduct fp32 0x26000001 0x25000001).value = (0x0b800002#32,0#32) ∧
    (certifiedTwoProduct? fp32 0x26000001 0x25000001).isNone = true ∧
    (productResidual fp32 0x26000001 0x25000001).flags .underflow = true ∧
    (twoProduct fp64 0x21a0000000000001 0x2190000000000001).value = (0x0340000000000002#64,0#64) ∧
    (certifiedTwoProduct? fp64 0x21a0000000000001 0x2190000000000001).isNone = true := by decide +kernel

/-- Normal rounded products can have residual underflow in either format. -/
example : (twoProduct fp32 0x00800001 0x3f800001).value = (0x00800002#32,0#32) ∧
    (certifiedTwoProduct? fp32 0x00800001 0x3f800001).isNone = true ∧
    (twoProduct fp64 0x0010000000000001 0x3ff0000000000001).value = (0x0010000000000002#64,0#64) ∧
    (certifiedTwoProduct? fp64 0x0010000000000001 0x3ff0000000000001).isNone = true := by decide +kernel

/-- The static exponent test is sufficient, not necessary for exactness. -/
example : ¬ TwoProductRange fp32 0x00800001 0x3f800000 ∧
    (certifiedTwoProduct? fp32 0x00800001 0x3f800000).isSome = true ∧
    TwoProductRange fp32 0x80000000 0x7f7fffff ∧
    TwoProductRange fp64 0x8000000000000000 0x7fefffffffffffff ∧
    ¬ TwoProductRange fp32 0x7f7fffff 0x40000000 ∧
    ¬ TwoProductRange fp64 0x7ff0000000000000 0 := by decide +kernel

/-- A general numerical theorem about the actual FMA residual, without certificate success. -/
example (a b : fp32.Word) (x y p : ℚ)
    (ha : (Datum.decode fp32 a).toRat? = some x) (hb : (Datum.decode fp32 b).toRat? = some y)
    (hp : (Datum.decode fp32 (mul fp32 .nearestEven a b).value).toRat? = some p) :
    ∃ e : ℚ, (Datum.decode fp32 (productResidual fp32 a b).value).toRat? = some e ∧
      |((x*y-p-e : ℚ) : ℝ)| ≤ fp32.format.minSubnormal/2 :=
  twoProduct_bounded_of_finite fp32 a b x y p ha hb hp

example (a b : fp64.Word) (x y p : ℚ)
    (ha : (Datum.decode fp64 a).toRat? = some x) (hb : (Datum.decode fp64 b).toRat? = some y)
    (hp : (Datum.decode fp64 (mul fp64 .nearestEven a b).value).toRat? = some p) :
    ∃ e : ℚ, (Datum.decode fp64 (productResidual fp64 a b).value).toRat? = some e ∧
      |((x*y-p-e : ℚ) : ℝ)| ≤ fp64.format.minSubnormal/2 :=
  twoProduct_bounded_of_finite fp64 a b x y p ha hb hp

end FP.IEEE.Software.Tests
