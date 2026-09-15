import FP.IEEE.Spec.Arithmetic
import FP.Summation

/-! Evaluation relations for explicit arithmetic schedules. These describe
compositions of IEEE operations, not the optional IEEE Clause 9 reduction APIs. -/
namespace FP.IEEE.Spec
open Interchange

inductive SumEvaluation (I : Interchange) (mode : RoundingMode) (a : ℕ → I.Word) :
    ReductionTree → Result I.Word → Prop where
  | zero : SumEvaluation I mode a .zero (Result.pure (Datum.zero false).encode)
  | input (i) : SumEvaluation I mode a (.input i) (Result.pure (a i))
  | add {l r} {lr rr out : Result I.Word} :
      SumEvaluation I mode a l lr → SumEvaluation I mode a r rr →
      Arithmetic I .add mode lr.value rr.value out →
      SumEvaluation I mode a (.add l r)
        ⟨out.value, Flags.union lr.flags (Flags.union rr.flags out.flags)⟩

inductive DotEvaluation (I : Interchange) (mode : RoundingMode) (a b : ℕ → I.Word) :
    ℕ → Result I.Word → Prop where
  | zero : DotEvaluation I mode a b 0 (Result.pure (Datum.zero false).encode)
  | succ {n} {acc prod out : Result I.Word} :
      DotEvaluation I mode a b n acc →
      Arithmetic I .mul mode (a n) (b n) prod →
      Arithmetic I .add mode acc.value prod.value out →
      DotEvaluation I mode a b (n + 1)
        ⟨out.value, Flags.union acc.flags (Flags.union prod.flags out.flags)⟩

end FP.IEEE.Spec
