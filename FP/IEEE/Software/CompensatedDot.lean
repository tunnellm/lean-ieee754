import FP.IEEE.Software.ProductBounds
import FP.IEEE.Software.TwoSumExact
import FP.IEEE.Spec.CompensatedDot

/-! Total online Dot2 execution and operation-local sticky flags. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

structure DotStepTrace (I : Interchange) where
  product : Result (I.Word × I.Word)
  sum : TwoSumTrace I
  combined : Result I.Word
  correction : Result I.Word

def dotStepTrace (I : Interchange) [I.Valid] (s c a b : I.Word) : DotStepTrace I :=
  let p := twoProduct I a b
  let h := twoSumTrace I s p.value.1
  let t := add I .nearestEven p.value.2 h.error.value
  let d := add I .nearestEven c t.value
  ⟨p,h,t,d⟩

def DotStepTrace.result {I : Interchange} (t : DotStepTrace I) : Result (I.Word × I.Word) :=
  ⟨(t.sum.sum.value,t.correction.value),
    t.product.flags.union (t.sum.flags.union (t.combined.flags.union t.correction.flags))⟩

def compensatedDotStep (I : Interchange) [I.Valid] (s c a b : I.Word) : Result (I.Word × I.Word) :=
  (dotStepTrace I s c a b).result

def compensatedDotCore (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : ℕ → Result (I.Word × I.Word)
  | 0 => Result.pure ((Datum.zero false).encode,(Datum.zero false).encode)
  | n+1 => (compensatedDotCore I a b n).bind fun p => compensatedDotStep I p.1 p.2 (a n) (b n)

def compensatedDot (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Result I.Word :=
  (compensatedDotCore I a b n).bind fun p => add I .nearestEven p.1 p.2

/-- A paired list has no mismatched lengths and consumes every pair exactly once. -/
def compensatedDotList (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word)) : Result I.Word :=
  compensatedDot I (fun i => (xs[i]?.getD (0,0)).1) (fun i => (xs[i]?.getD (0,0)).2) xs.length

theorem compensatedDotStep_spec (I : Interchange) [I.Valid] (s c a b : I.Word) :
    Spec.CompensatedDotStep I s c a b (compensatedDotStep I s c a b) := by
  exact ⟨twoProduct I a b,twoSum I s (twoProduct I a b).value.1,
    (dotStepTrace I s c a b).combined,(dotStepTrace I s c a b).correction,
    twoProduct_spec I a b,twoSum_spec I s _,add_spec I .nearestEven _ _,add_spec I .nearestEven _ _,rfl,rfl⟩

theorem compensatedDotCore_spec (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) :
    Spec.CompensatedDotPass I a b n (compensatedDotCore I a b n) := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .succ ih (compensatedDotStep_spec I _ _ _ _)

theorem compensatedDot_spec (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) :
    Spec.CompensatedDotEvaluation I a b n (compensatedDot I a b n) :=
  ⟨_,_,compensatedDotCore_spec I a b n,add_spec I .nearestEven _ _,rfl⟩

/-- Ten arithmetic events: multiply/FMA, six TwoSum stages, and two correction additions.
Quiet negation contributes no flags. -/
def dotStepEvents (I : Interchange) [I.Valid] (s c a b : I.Word) : List Flags :=
  let t := dotStepTrace I s c a b
  [(mul I .nearestEven a b).flags,(productResidual I a b).flags,
    t.sum.sum.flags,t.sum.bvirt.flags,t.sum.avirt.flags,t.sum.bround.flags,t.sum.around.flags,t.sum.error.flags,
    t.combined.flags,t.correction.flags]

theorem compensatedDotStep_flags_iff (I : Interchange) [I.Valid] (s c a b : I.Word) (e : Exception) :
    (compensatedDotStep I s c a b).flags e = true ↔ ∃ f ∈ dotStepEvents I s c a b, f e = true := by
  simp [compensatedDotStep,DotStepTrace.result,dotStepEvents,dotStepTrace,twoProduct,TwoSumTrace.flags,
    Flags.union,Bool.or_eq_true,or_assoc]

def compensatedDotCoreEvents (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : ℕ → List Flags
  | 0 => []
  | n+1 => compensatedDotCoreEvents I a b n ++
      dotStepEvents I (compensatedDotCore I a b n).value.1 (compensatedDotCore I a b n).value.2 (a n) (b n)

def compensatedDotEvents (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : List Flags :=
  compensatedDotCoreEvents I a b n ++
    [(add I .nearestEven (compensatedDotCore I a b n).value.1 (compensatedDotCore I a b n).value.2).flags]

theorem compensatedDotCore_flags_iff (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) (e : Exception) :
    (compensatedDotCore I a b n).flags e = true ↔ ∃ f ∈ compensatedDotCoreEvents I a b n, f e = true := by
  induction n with
  | zero => simp [compensatedDotCore,compensatedDotCoreEvents,Result.pure,Flags.empty]
  | succ n ih =>
    simp [compensatedDotCore,compensatedDotCoreEvents,Result.bind,Flags.union,ih,
      compensatedDotStep_flags_iff,or_and_right,exists_or]

theorem compensatedDot_flags_iff (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) (e : Exception) :
    (compensatedDot I a b n).flags e = true ↔ ∃ f ∈ compensatedDotEvents I a b n, f e = true := by
  simp [compensatedDot,compensatedDotEvents,Result.bind,Flags.union,compensatedDotCore_flags_iff,
    or_and_right,exists_or]

end FP.IEEE.Software
