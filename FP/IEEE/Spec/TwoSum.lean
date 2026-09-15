import FP.IEEE.Spec.Arithmetic

/-! The classical six-operation TwoSum evaluation schedule, independently specified. -/
namespace FP.IEEE.Spec

def TwoSum (I : Interchange) (a b : I.Word) (r : Result (I.Word × I.Word)) : Prop :=
  ∃ s bv av br ar e : Result I.Word,
    Arithmetic I .add .nearestEven a b s ∧
    Arithmetic I .sub .nearestEven s.value a bv ∧
    Arithmetic I .sub .nearestEven s.value bv.value av ∧
    Arithmetic I .sub .nearestEven b bv.value br ∧
    Arithmetic I .sub .nearestEven a av.value ar ∧
    Arithmetic I .add .nearestEven ar.value br.value e ∧
    r.value = (s.value,e.value) ∧
    r.flags = s.flags.union (bv.flags.union (av.flags.union (br.flags.union (ar.flags.union e.flags))))
end FP.IEEE.Spec
