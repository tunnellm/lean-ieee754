import FP.IEEE.Spec.Nearest

/-! Mode-parametric real rounding and IEEE range-event predicates.
Overflow and after-rounding tininess use precision rounding with no exponent
bounds. These definitions do not import the executable software implementation. -/
noncomputable section
open scoped Classical
namespace FP.IEEE.Spec

/-- Mathematical integer rounding for each supported IEEE rounding direction. -/
def roundInteger (mode : RoundingMode) (x : ℝ) : ℤ :=
  match mode with
  | .nearestEven => roundEven x
  | .towardNegative => ⌊x⌋
  | .towardPositive => ⌈x⌉
  | .towardZero => if x < 0 then ⌈x⌉ else ⌊x⌋
  | .nearestAway =>
    let k := ⌊x⌋
    if x - k < 1 / 2 then k
    else if 1 / 2 < x - k then k + 1
    else if x < 0 then k else k + 1

/-- Precision rounding with gradual underflow, before upper range handling. -/
def roundWithMode (F : Format) (mode : RoundingMode) (x : ℝ) : ℝ :=
  (roundInteger mode (x / F.quantum x) : ℝ) * F.quantum x

/-- Fixed precision, with neither an upper nor a lower exponent bound. -/
def precisionRoundWithMode (F : Format) (mode : RoundingMode) (x : ℝ) : ℝ :=
  let h := (2 : ℝ) ^ (Int.log 2 |x| - F.fractionBits)
  (roundInteger mode (x / h) : ℝ) * h

def OverflowWithMode (F : Format) (mode : RoundingMode) (x : ℝ) : Prop :=
  F.maxFinite < |precisionRoundWithMode F mode x|

def TinyWithMode (F : Format) (mode : RoundingMode) (x : ℝ) : Prop :=
  0 < |precisionRoundWithMode F mode x| ∧
    |precisionRoundWithMode F mode x| < F.minNormal

/-- The default overflow result is infinite exactly in these cases. -/
def OverflowToInfinity (mode : RoundingMode) (negative : Bool) : Prop :=
  mode = .nearestEven ∨ mode = .nearestAway ∨
    (mode = .towardNegative ∧ negative = true) ∨
    (mode = .towardPositive ∧ negative = false)

@[simp] theorem roundWithMode_even (F : Format) (x : ℝ) :
    roundWithMode F .nearestEven x = F.roundFinite x := rfl

@[simp] theorem precisionRoundWithMode_even (F : Format) (x : ℝ) :
    precisionRoundWithMode F .nearestEven x = precisionRound F x := rfl

/-- Operation-local default flags for rounding an exact finite input. -/
structure RoundingFlags (F : Format) (mode : RoundingMode) (x : ℝ) (flags : Flags) : Prop where
  invalid : flags .invalid = false
  divideByZero : flags .divideByZero = false
  overflow : flags .overflow = true ↔ OverflowWithMode F mode x
  inexact : flags .inexact = true ↔ OverflowWithMode F mode x ∨ roundWithMode F mode x ≠ x
  underflow : flags .underflow = true ↔
    ¬ OverflowWithMode F mode x ∧ roundWithMode F mode x ≠ x ∧ TinyWithMode F mode x

/-- Total rounding of an exact finite input, with default exception handling.
The range predicates use the unbounded exponent range required by Clause 7. -/
structure Rounding (I : Interchange) (mode : RoundingMode) (x : ℝ) (zeroSign : Bool)
    (result : Result I.Word) : Prop where
  finite : ¬ OverflowWithMode I.format mode x →
    I.decode? result.value = some (roundWithMode I.format mode x)
  overflow_infinite : OverflowWithMode I.format mode x →
    OverflowToInfinity mode (realSign x zeroSign) →
    Interchange.Datum.decode I result.value = .infinity (realSign x zeroSign)
  overflow_finite : OverflowWithMode I.format mode x →
    ¬ OverflowToInfinity mode (realSign x zeroSign) →
    I.decode? result.value = some
      (if realSign x zeroSign then -I.format.maxFinite else I.format.maxFinite)
  sign : I.negative result.value =
    if OverflowWithMode I.format mode x then realSign x zeroSign
    else realSign (roundWithMode I.format mode x) (realSign x zeroSign)
  flags : RoundingFlags I.format mode x result.flags

end FP.IEEE.Spec
