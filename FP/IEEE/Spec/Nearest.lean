import FP.IEEE.Projection
import FP.IEEE.Environment

/-! Real-valued contract for nearest-even rounding of a finite exact input.
The contract specifies the finite projection, signed overflow/zero results,
and default flags. Tininess is measured after precision rounding with an
unbounded exponent range, not by classifying the final subnormal result. -/
noncomputable section
open scoped Classical
namespace FP.IEEE.Spec

def precisionRound (F : Format) (x : ℝ) : ℝ :=
  let h := (2 : ℝ) ^ (Int.log 2 |x| - F.fractionBits)
  (roundEven (x / h) : ℝ) * h

def TinyAfter (F : Format) (x : ℝ) : Prop :=
  0 < |precisionRound F x| ∧ |precisionRound F x| < F.minNormal

def realSign (x : ℝ) (zeroSign : Bool) : Bool :=
  if x = 0 then zeroSign else decide (x < 0)

/-- The numerical overflow boundary is the previously specified IEEE
nearest-even midpoint; overflow always raises inexact under default handling. -/
structure NearestRounding (I : Interchange) (x : ℝ) (zeroSign : Bool)
    (result : Result I.Word) : Prop where
  value : I.decode? result.value = I.format.round? x
  sign : I.negative result.value =
    if |x| < I.format.overflowThreshold then
      realSign (I.format.roundFinite x) (realSign x zeroSign)
    else realSign x zeroSign
  overflow_result : ¬ |x| < I.format.overflowThreshold →
    Interchange.Datum.decode I result.value = .infinity (realSign x zeroSign)
  invalid : result.flags .invalid = false
  divideByZero : result.flags .divideByZero = false
  overflow : result.flags .overflow = true ↔ ¬ |x| < I.format.overflowThreshold
  inexact : result.flags .inexact = true ↔
    ¬ |x| < I.format.overflowThreshold ∨ I.format.roundFinite x ≠ x
  underflow : result.flags .underflow = true ↔
    |x| < I.format.overflowThreshold ∧ I.format.roundFinite x ≠ x ∧ TinyAfter I.format x

end FP.IEEE.Spec
