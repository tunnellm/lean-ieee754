import FP.IEEE.Spec.TwoSum

/-! IEEE evaluation relations for online compensated summation. -/
namespace FP.IEEE.Spec

inductive CompensatedPassEvaluation (I : Interchange) :
    I.Word → I.Word → List I.Word → Result (I.Word × I.Word) → Prop where
  | nil (s c : I.Word) : CompensatedPassEvaluation I s c [] (Result.pure (s,c))
  | cons {s c a : I.Word} {xs : List I.Word} {t : Result (I.Word × I.Word)}
      {correction : Result I.Word} {r : Result (I.Word × I.Word)}
      (ht : TwoSum I s a t) (hc : Arithmetic I .add .nearestEven c t.value.2 correction)
      (hr : CompensatedPassEvaluation I t.value.1 correction.value xs r) :
      CompensatedPassEvaluation I s c (a::xs)
        ⟨r.value,t.flags.union (correction.flags.union r.flags)⟩

def CompensatedSumEvaluation (I : Interchange) (xs : List I.Word) (r : Result I.Word) : Prop :=
  ∃ p : Result (I.Word × I.Word), ∃ f : Result I.Word,
    CompensatedPassEvaluation I (Interchange.Datum.zero false).encode
      (Interchange.Datum.zero false).encode xs p ∧
    Arithmetic I .add .nearestEven p.value.1 p.value.2 f ∧
    r = ⟨f.value,p.flags.union f.flags⟩
end FP.IEEE.Spec
