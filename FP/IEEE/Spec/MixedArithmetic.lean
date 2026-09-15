import FP.IEEE.Spec.Conversion

/-! Mixed source/destination arithmetic: the exact source values are combined
before one rounding in the destination. NaN payload mapping is explicit. -/
namespace FP.IEEE.Spec
open Interchange
noncomputable section

def mixedCase (A B : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) : ArithmeticCase ℝ :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  let zeroSign := if op = .mul then sa ^^ sb
    else if a.isZero && b.isZero && (sa == sb) then sa else decide (mode = .towardNegative)
  if a.isNaN || b.isNaN then .nan
  else if op = .mul then
    if (a.isZero && b.isInfinite) || (a.isInfinite && b.isZero) then .invalid
    else if a.isInfinite || b.isInfinite then .infinity (sa ^^ sb)
    else .finite (binaryExact op (A.value a.encode) (B.value b.encode)) zeroSign
  else if a.isInfinite && b.isInfinite && (sa != sb) then .invalid
  else if a.isInfinite then .infinity sa
  else if b.isInfinite then .infinity sb
  else .finite (binaryExact op (A.value a.encode) (B.value b.encode)) zeroSign

/-- First signaling operand, otherwise first quiet operand, across two formats. -/
def chooseLeftNaN {A B : Interchange} (a : Datum A) (b : Datum B) : Bool :=
  a.isSignaling || (!b.isSignaling && a.isNaN)

def MixedNaN (A B D : Interchange) (a : Datum A) (b : Datum B) (r : Result D.Word) : Prop :=
  (if chooseLeftNaN a b then ConvertedNaN A D a r.value else ConvertedNaN B D b r.value) ∧
    r.flags .invalid = (a.isSignaling || b.isSignaling) ∧
    ∀ e, e ≠ .invalid → r.flags e = false

def MixedArithmeticResult (A B D : Interchange) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : ArithmeticCase ℝ) (r : Result D.Word) : Prop :=
  match c with
  | .nan => MixedNaN A B D a b r
  | .invalid => InvalidResult D r
  | .infinity s => Datum.decode D r.value = .infinity s ∧ r.flags = Flags.empty
  | .finite x s => Rounding D mode x s r

def MixedArithmetic (A B D : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (r : Result D.Word) : Prop :=
  MixedArithmeticResult A B D mode (Datum.decode A a) (Datum.decode B b)
    (mixedCase A B op mode (Datum.decode A a) (Datum.decode B b)) r

end
end FP.IEEE.Spec
