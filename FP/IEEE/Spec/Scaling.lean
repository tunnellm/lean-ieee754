import FP.IEEE.Spec.Conversion

/-! Independent real contract for power-of-two scaling. -/
namespace FP.IEEE.Spec
open Interchange
noncomputable section

def ScaleB (A D : Interchange) (mode : RoundingMode) (a : A.Word) (n : ℤ) (r : Result D.Word) : Prop :=
  let d := Datum.decode A a
  if d.isNaN then ConvertedNaN A D d r.value ∧ r.flags .invalid = d.isSignaling ∧
    ∀ e, e ≠ .invalid → r.flags e = false
  else if d.isInfinite then Datum.decode D r.value = .infinity d.fields.negative ∧ r.flags = Flags.empty
  else Rounding D mode (A.value a * (2 : ℝ)^n) d.fields.negative r
end
end FP.IEEE.Spec
