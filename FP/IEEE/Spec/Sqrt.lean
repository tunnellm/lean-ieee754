import FP.IEEE.Spec.Conversion
import FP.IEEE.Spec.RealRounding

/-! Independent real square-root contract, including signed zero and exceptional operands. -/
namespace FP.IEEE.Spec
open Interchange
noncomputable section

def Sqrt (A D : Interchange) (mode : RoundingMode) (a : A.Word) (r : Result D.Word) : Prop :=
  let d := Datum.decode A a
  if d.isNaN then
    ConvertedNaN A D d r.value ∧ r.flags .invalid = d.isSignaling ∧
      ∀ e, e ≠ .invalid → r.flags e = false
  else if d.isZero then
    Datum.decode D r.value = .zero d.fields.negative ∧ r.flags = Flags.empty
  else if d.isInfinite then
    if d.fields.negative then InvalidResult D r
    else Datum.decode D r.value = .infinity false ∧ r.flags = Flags.empty
  else if A.value a < 0 then InvalidResult D r
  else Rounding D mode (Real.sqrt (A.value a)) false r
end
end FP.IEEE.Spec
