import FP.IEEE.Software.Arithmetic
import FP.IEEE.Software.Reductions
import FP.IEEE.Spec.Reductions

/-! Total scheduled reductions on interchange words. Computation continues
through exceptional results; every operation's flags are accumulated. -/
namespace FP.IEEE.Software
open Interchange

/-- Empty trees return +0; singleton leaves are copied without an arithmetic
operation, so a singleton signaling NaN is preserved without raising invalid. -/
def sumTree (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word) :
    ReductionTree → Result I.Word
  | .zero => Result.pure (Datum.zero false).encode
  | .input i => Result.pure (a i)
  | .add l r => (sumTree I mode a l).bind fun x =>
      (sumTree I mode a r).bind fun y => add I mode x y

def sequentialSum (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word) (n : ℕ) :
    Result I.Word := sumTree I mode a (sequentialTree 0 n)

def pairwiseSum (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word) (n : ℕ) :
    Result I.Word := sumTree I mode a (pairwiseTree 0 n)

/-- Zero-started dot product with separate multiplication and addition. -/
def dot (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : ℕ → I.Word) : ℕ → Result I.Word
  | 0 => Result.pure (Datum.zero false).encode
  | n + 1 => (dot I mode a b n).bind fun acc =>
      (mul I mode (a n) (b n)).bind fun prod => add I mode acc prod

theorem sumTree_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word)
    (t : ReductionTree) : Spec.SumEvaluation I mode a t (sumTree I mode a t) := by
  induction t with
  | zero => exact .zero
  | input i => exact .input i
  | add l r hl hr => exact .add hl hr (add_spec I mode _ _)

theorem sequentialSum_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word)
    (n : ℕ) : Spec.SumEvaluation I mode a (sequentialTree 0 n) (sequentialSum I mode a n) :=
  sumTree_spec I mode a _

theorem pairwiseSum_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word)
    (n : ℕ) : Spec.SumEvaluation I mode a (pairwiseTree 0 n) (pairwiseSum I mode a n) :=
  sumTree_spec I mode a _

theorem dot_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : ℕ → I.Word) (n : ℕ) :
    Spec.DotEvaluation I mode a b n (dot I mode a b n) := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .succ ih (mul_spec I mode _ _) (add_spec I mode _ _)

/-- The exact list of operation-local flag sets in evaluation order. -/
def sumEvents (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word) :
    ReductionTree → List Flags
  | .zero | .input _ => []
  | .add l r => sumEvents I mode a l ++ sumEvents I mode a r ++
      [(add I mode (sumTree I mode a l).value (sumTree I mode a r).value).flags]

def dotEvents (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : ℕ → I.Word) : ℕ → List Flags
  | 0 => []
  | n + 1 => dotEvents I mode a b n ++ [(mul I mode (a n) (b n)).flags,
      (add I mode (dot I mode a b n).value (mul I mode (a n) (b n)).value).flags]

/-- A final flag is set exactly when an executed operation raised it. -/
theorem sumTree_flags_iff (I : Interchange) [I.Valid] (mode : RoundingMode) (a : ℕ → I.Word)
    (t : ReductionTree) (e : Exception) :
    (sumTree I mode a t).flags e = true ↔ ∃ f ∈ sumEvents I mode a t, f e = true := by
  induction t with
  | zero => simp [sumTree, sumEvents, Result.pure, Flags.empty]
  | input i => simp [sumTree, sumEvents, Result.pure, Flags.empty]
  | add l r hl hr =>
    simp [sumTree, sumEvents, Result.bind, Flags.union, hl, hr, or_and_right, exists_or]

theorem dot_flags_iff (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : ℕ → I.Word)
    (n : ℕ) (e : Exception) :
    (dot I mode a b n).flags e = true ↔ ∃ f ∈ dotEvents I mode a b n, f e = true := by
  induction n with
  | zero => simp [dot, dotEvents, Result.pure, Flags.empty]
  | succ n ih => simp [dot, dotEvents, Result.bind, Flags.union, ih, or_and_right, exists_or]

/-- Success of the old finite evaluator implies the same decoded total result.
The total evaluator additionally retains exceptional results and flags. -/
theorem sumTree_projection_of_some (I : Interchange) [I.Valid] (a : ℕ → I.Word)
    (t : ReductionTree) (q : ℚ) (h : wordSumTree? I a t = some q) :
    (Datum.decode I (sumTree I .nearestEven a t).value).toRat? = some q := by
  induction t generalizing q with
  | zero => simpa [sumTree, wordSumTree?, Result.pure] using h
  | input i => exact h
  | add l r hl hr =>
    change ((wordSumTree? I a l).bind fun x => (wordSumTree? I a r).bind fun y =>
      roundNearest? I.format (x + y)) = some q at h
    cases hL : wordSumTree? I a l with
    | none => simp [hL] at h
    | some x =>
      cases hR : wordSumTree? I a r with
      | none => simp [hR] at h
      | some y =>
        have hs : roundNearest? I.format (x + y) = some q := by simpa [hL, hR] using h
        exact (binary_even_projection I .add _ _ x y (hl x hL) (hr y hR)).trans hs

theorem dot_projection_of_some (I : Interchange) [I.Valid] (a b : ℕ → I.Word)
    (n : ℕ) (q : ℚ) (h : wordDot? I a b n = some q) :
    (Datum.decode I (dot I .nearestEven a b n).value).toRat? = some q := by
  induction n generalizing q with
  | zero => simpa [dot, wordDot?, Result.pure] using h
  | succ n ih =>
    change ((wordDot? I a b n).bind fun s =>
      ((Datum.decode I (a n)).toRat?.bind fun x => (Datum.decode I (b n)).toRat?.bind fun y =>
        roundNearest? I.format (x * y)).bind fun p => roundNearest? I.format (s + p)) = some q at h
    cases hs : wordDot? I a b n with
    | none => simp [hs] at h
    | some s =>
      cases hx : (Datum.decode I (a n)).toRat? with
      | none => simp [hs, hx] at h
      | some x =>
        cases hy : (Datum.decode I (b n)).toRat? with
        | none => simp [hs, hx, hy] at h
        | some y =>
          cases hp : roundNearest? I.format (x * y) with
          | none => simp [hs, hx, hy, hp] at h
          | some p =>
            have hprod := (binary_even_projection I .mul (a n) (b n) x y hx hy).trans hp
            have hadd : roundNearest? I.format (s + p) = some q := by simpa [hs, hx, hy, hp] using h
            exact (binary_even_projection I .add _ _ s p (ih s hs) hprod).trans hadd

end FP.IEEE.Software
