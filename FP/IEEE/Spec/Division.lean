import FP.IEEE.Spec.MixedArithmetic

/-! Total binary division, with independent source/destination formats.
In particular, infinity divided by zero is exact infinity without divideByZero. -/
namespace FP.IEEE
inductive DivisionCase (α : Type) where
  | nan | invalid | infinity (negative : Bool) | zero (negative : Bool)
  | divideByZero (negative : Bool) | finite (exact : α) (zeroSign : Bool)
namespace DivisionCase
def map (f : α → β) : DivisionCase α → DivisionCase β
  | .nan => .nan
  | .invalid => .invalid
  | .infinity s => .infinity s
  | .zero s => .zero s
  | .divideByZero s => .divideByZero s
  | .finite x s => .finite (f x) s
end DivisionCase
namespace Spec
open Interchange
noncomputable section

def divisionCase (A B : Interchange) (a : Datum A) (b : Datum B) : DivisionCase ℝ :=
  let sign := a.fields.negative ^^ b.fields.negative
  if a.isNaN || b.isNaN then .nan
  else if (a.isInfinite && b.isInfinite) || (a.isZero && b.isZero) then .invalid
  else if a.isInfinite then .infinity sign
  else if b.isInfinite then .zero sign
  else if b.isZero then .divideByZero sign
  else .finite (A.value a.encode / B.value b.encode) sign

def DivisionResult (A B D : Interchange) (mode : RoundingMode) (a : Datum A) (b : Datum B)
    (c : DivisionCase ℝ) (r : Result D.Word) : Prop :=
  match c with
  | .nan => MixedNaN A B D a b r
  | .invalid => InvalidResult D r
  | .infinity s => Datum.decode D r.value = .infinity s ∧ r.flags = Flags.empty
  | .zero s => Datum.decode D r.value = .zero s ∧ r.flags = Flags.empty
  | .divideByZero s => Datum.decode D r.value = .infinity s ∧
      ∀ e, r.flags e = true ↔ e = .divideByZero
  | .finite x s => Rounding D mode x s r

def Division (A B D : Interchange) (mode : RoundingMode) (a : A.Word) (b : B.Word)
    (r : Result D.Word) : Prop :=
  DivisionResult A B D mode (Datum.decode A a) (Datum.decode B b)
    (divisionCase A B (Datum.decode A a) (Datum.decode B b)) r

end
end Spec
end FP.IEEE
