import FP.IEEE.Spec.TwoProduct
import FP.IEEE.Spec.TwoSum

/-! The zero-started online Dot2 schedule, independently specified. -/
namespace FP.IEEE.Spec
open Interchange

def CompensatedDotStep (I : Interchange) (s c a b : I.Word) (r : Result (I.Word × I.Word)) : Prop :=
  ∃ p h : Result (I.Word × I.Word), ∃ t d : Result I.Word,
    TwoProduct I a b p ∧ TwoSum I s p.value.1 h ∧
    Arithmetic I .add .nearestEven p.value.2 h.value.2 t ∧
    Arithmetic I .add .nearestEven c t.value d ∧
    r.value = (h.value.1,d.value) ∧
    r.flags = p.flags.union (h.flags.union (t.flags.union d.flags))

inductive CompensatedDotPass (I : Interchange) (a b : ℕ → I.Word) :
    ℕ → Result (I.Word × I.Word) → Prop where
  | zero : CompensatedDotPass I a b 0
      (Result.pure ((Datum.zero false).encode,(Datum.zero false).encode))
  | succ {n : ℕ} {p r : Result (I.Word × I.Word)}
      (hp : CompensatedDotPass I a b n p)
      (hr : CompensatedDotStep I p.value.1 p.value.2 (a n) (b n) r) :
      CompensatedDotPass I a b (n+1) ⟨r.value,p.flags.union r.flags⟩

def CompensatedDotEvaluation (I : Interchange) (a b : ℕ → I.Word) (n : ℕ) (r : Result I.Word) : Prop :=
  ∃ p : Result (I.Word × I.Word), ∃ q : Result I.Word,
    CompensatedDotPass I a b n p ∧ Arithmetic I .add .nearestEven p.value.1 p.value.2 q ∧
    r = ⟨q.value,p.flags.union q.flags⟩

end FP.IEEE.Spec
