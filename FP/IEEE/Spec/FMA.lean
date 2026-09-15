import FP.IEEE.Spec.MixedArithmetic

/-! Fused multiply-add: exact multiplication and addition followed by one rounding.
The binding raises invalid for zero times infinity even with a quiet-NaN addend. -/
namespace FP.IEEE.Spec
open Interchange
noncomputable section

def invalidProduct {A B : Interchange} (a : Datum A) (b : Datum B) : Bool :=
  (a.isZero && b.isInfinite) || (a.isInfinite && b.isZero)

def fmaZeroSign {A B C : Interchange} (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) : Bool :=
  let s := a.fields.negative ^^ b.fields.negative
  if (a.isZero || b.isZero) && c.isZero && (s == c.fields.negative) then s
  else decide (mode = .towardNegative)

def fmaCase (A B C : Interchange) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) : ArithmeticCase ℝ :=
  let s := a.fields.negative ^^ b.fields.negative
  if a.isNaN || b.isNaN || c.isNaN then .nan
  else if invalidProduct a b then .invalid
  else if (a.isInfinite || b.isInfinite) && c.isInfinite && (s != c.fields.negative) then .invalid
  else if a.isInfinite || b.isInfinite then .infinity s
  else if c.isInfinite then .infinity c.fields.negative
  else .finite (A.value a.encode * B.value b.encode + C.value c.encode) (fmaZeroSign mode a b c)

/-- First signaling NaN, otherwise first quiet NaN, in operand order. -/
def FmaNaN (A B C D : Interchange) (a : Datum A) (b : Datum B) (c : Datum C)
    (r : Result D.Word) : Prop :=
  (if a.isSignaling then ConvertedNaN A D a r.value
   else if b.isSignaling then ConvertedNaN B D b r.value
   else if c.isSignaling then ConvertedNaN C D c r.value
   else if a.isNaN then ConvertedNaN A D a r.value
   else if b.isNaN then ConvertedNaN B D b r.value
   else ConvertedNaN C D c r.value) ∧
  r.flags .invalid = (a.isSignaling || b.isSignaling || c.isSignaling || invalidProduct a b) ∧
  ∀ e, e ≠ .invalid → r.flags e = false

def FmaResult (A B C D : Interchange) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) (k : ArithmeticCase ℝ) (r : Result D.Word) : Prop :=
  match k with
  | .nan => FmaNaN A B C D a b c r
  | .invalid => InvalidResult D r
  | .infinity s => Datum.decode D r.value = .infinity s ∧ r.flags = Flags.empty
  | .finite x s => Rounding D mode x s r

def Fma (A B C D : Interchange) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (c : C.Word) (r : Result D.Word) : Prop :=
  FmaResult A B C D mode (Datum.decode A a) (Datum.decode B b) (Datum.decode C c)
    (fmaCase A B C mode (Datum.decode A a) (Datum.decode B b) (Datum.decode C c)) r
end
end FP.IEEE.Spec
