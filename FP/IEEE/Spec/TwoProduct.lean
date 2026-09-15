import FP.IEEE.Spec.FMA

/-! Independent multiply, quiet-negate, and FMA schedule for TwoProduct. -/
namespace FP.IEEE.Spec
open Interchange

def TwoProduct (I : Interchange) (a b : I.Word) (r : Result (I.Word × I.Word)) : Prop :=
  ∃ p e : Result I.Word,
    Arithmetic I .mul .nearestEven a b p ∧
    Fma I I I I .nearestEven a b
      ((Datum.decode I p.value).withSign (!(Datum.decode I p.value).fields.negative)).encode e ∧
    r.value = (p.value,e.value) ∧ r.flags = p.flags.union e.flags

end FP.IEEE.Spec
