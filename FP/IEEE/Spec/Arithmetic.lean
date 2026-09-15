import FP.IEEE.Spec.RoundingModes

/-! Total same-format add/subtract/multiply contracts, including Clause 6
special results and the project's deterministic NaN selection policy. -/
namespace FP.IEEE
inductive BinaryOp where
  | add | sub | mul
  deriving DecidableEq, Repr

inductive ArithmeticCase (α : Type) where
  | nan | invalid | infinity (negative : Bool) | finite (exact : α) (zeroSign : Bool)

namespace ArithmeticCase
def map (f : α → β) : ArithmeticCase α → ArithmeticCase β
  | .nan => .nan
  | .invalid => .invalid
  | .infinity s => .infinity s
  | .finite x s => .finite (f x) s
end ArithmeticCase

namespace Spec
open Interchange
noncomputable section

def binaryExact (op : BinaryOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y

/-- The second sign is inverted for subtraction only after NaN selection.
Same-signed zero addends retain their sign; cancellation uses the direction. -/
def arithmeticCase (I : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a b : Datum I) : ArithmeticCase ℝ :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  let zeroSign := if op = .mul then sa ^^ sb
    else if a.isZero && b.isZero && (sa == sb) then sa else decide (mode = .towardNegative)
  if a.isNaN || b.isNaN then .nan
  else if op = .mul then
    if (a.isZero && b.isInfinite) || (a.isInfinite && b.isZero) then .invalid
    else if a.isInfinite || b.isInfinite then .infinity (sa ^^ sb)
    else .finite (binaryExact op (I.value a.encode) (I.value b.encode)) zeroSign
  else if a.isInfinite && b.isInfinite && (sa != sb) then .invalid
  else if a.isInfinite then .infinity sa
  else if b.isInfinite then .infinity sb
  else .finite (binaryExact op (I.value a.encode) (I.value b.encode)) zeroSign

def nanChoice {I : Interchange} (ds : List (Datum I)) : Option (Datum I) :=
  match ds.find? Datum.isSignaling with
  | some d => some d
  | none => ds.find? Datum.isNaN

structure NaNResult (I : Interchange) (ds : List (Datum I)) (r : Result I.Word) : Prop where
  quiet : (Datum.decode I r.value).classify = .quietNaN
  invalid : r.flags .invalid = ds.any Datum.isSignaling
  other : ∀ e, e ≠ .invalid → r.flags e = false
  selected : ∀ d, nanChoice ds = some d →
    (Datum.decode I r.value).fields.negative = d.fields.negative ∧
    I.payload (Datum.decode I r.value).fields.fraction = I.payload d.fields.fraction

structure InvalidResult (I : Interchange) (r : Result I.Word) : Prop where
  quiet : (Datum.decode I r.value).classify = .quietNaN
  positive : (Datum.decode I r.value).fields.negative = false
  payload : I.payload (Datum.decode I r.value).fields.fraction = 0
  flags : ∀ e, r.flags e = true ↔ e = .invalid

def ArithmeticResult (I : Interchange) (mode : RoundingMode) (ds : List (Datum I))
    (c : ArithmeticCase ℝ) (r : Result I.Word) : Prop :=
  match c with
  | .nan => NaNResult I ds r
  | .invalid => InvalidResult I r
  | .infinity s => Datum.decode I r.value = .infinity s ∧ r.flags = Flags.empty
  | .finite x s => Rounding I mode x s r

def Arithmetic (I : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (r : Result I.Word) : Prop :=
  ArithmeticResult I mode [Datum.decode I a, Datum.decode I b]
    (arithmeticCase I op mode (Datum.decode I a) (Datum.decode I b)) r

end
end Spec
end FP.IEEE
