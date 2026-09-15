import FP.IEEE.Spec.Arithmetic

/-! Binary format conversion, with the project's high-bit NaN payload alignment.
Alignment is a binding choice; the IEEE standard does not fix a unique payload mapping. -/
namespace FP.IEEE.Spec
open Interchange
noncomputable section

/-- Quiet NaN with source sign and high-aligned payload, including truncation. -/
structure ConvertedNaN (S D : Interchange) (d : Datum S) (w : D.Word) : Prop where
  quiet : (Datum.decode D w).classify = .quietNaN
  sign : (Datum.decode D w).fields.negative = d.fields.negative
  payload : (D.payload (Datum.decode D w).fields.fraction).toNat =
    (S.payload d.fields.fraction).toNat * 2^(D.format.fractionBits - 1) /
      2^(S.format.fractionBits - 1)

def Conversion (S D : Interchange) (mode : RoundingMode) (w : S.Word) (r : Result D.Word) : Prop :=
  let d := Datum.decode S w
  if d.isNaN then
    ConvertedNaN S D d r.value ∧ r.flags .invalid = d.isSignaling ∧
      ∀ e, e ≠ .invalid → r.flags e = false
  else if d.isInfinite then
    Datum.decode D r.value = .infinity d.fields.negative ∧ r.flags = Flags.empty
  else Rounding D mode (S.value w) d.fields.negative r

end
end FP.IEEE.Spec
