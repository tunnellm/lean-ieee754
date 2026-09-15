import FP.IEEE.Software.CompensatedSum
import FP.IEEE.Spec.Compensated
import FP.Range.Interval

/-! Total execution and transfer from numerical certificates to that execution. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def compensatedCore (I : Interchange) [I.Valid] (s c : I.Word) :
    List I.Word → Result (I.Word × I.Word)
  | [] => Result.pure (s,c)
  | a::xs => (twoSum I s a).bind fun t =>
      (add I .nearestEven c t.2).bind fun corr => compensatedCore I t.1 corr xs

def compensatedSum (I : Interchange) [I.Valid] (xs : List I.Word) : Result I.Word :=
  (compensatedCore I (Datum.zero false).encode (Datum.zero false).encode xs).bind
    fun p => add I .nearestEven p.1 p.2

theorem compensatedCore_spec (I : Interchange) [I.Valid] (xs : List I.Word) (s c : I.Word) :
    Spec.CompensatedPassEvaluation I s c xs (compensatedCore I s c xs) := by
  induction xs generalizing s c with
  | nil => exact .nil s c
  | cons a xs ih =>
    exact .cons (twoSum_spec I s a) (add_spec I .nearestEven _ _) (ih _ _)

theorem compensatedSum_spec (I : Interchange) [I.Valid] (xs : List I.Word) :
    Spec.CompensatedSumEvaluation I xs (compensatedSum I xs) := by
  exact ⟨_,_,compensatedCore_spec I xs _ _,add_spec I .nearestEven _ _,rfl⟩

theorem certifiedTwoSum?_execution (I : Interchange) [I.Valid] (a b : I.Word)
    (t : Result (I.Word × I.Word)) (ht : certifiedTwoSum? I a b = some t) : t = twoSum I a b := by
  unfold certifiedTwoSum? at ht
  dsimp only at ht
  split_ifs at ht
  exact (Option.some.inj ht).symm

theorem compensatedStep?_execution (I : Interchange) [I.Valid] (st : CompensationState I)
    (a : I.Word) (r : Result (CompensationState I)) (hr : compensatedStep? I st a = some r) :
    r.value.high = (twoSum I st.high a).value.1 ∧
    r.value.correction = (add I .nearestEven st.correction (twoSum I st.high a).value.2).value ∧
    r.flags = (twoSum I st.high a).flags.union
      (add I .nearestEven st.correction (twoSum I st.high a).value.2).flags := by
  unfold compensatedStep? at hr
  cases ht : certifiedTwoSum? I st.high a with
  | none => simp [ht] at hr
  | some t =>
    rw [ht] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    rw [certifiedTwoSum?_execution I st.high a t ht]
    exact ⟨rfl,rfl,rfl⟩

theorem compensatedAux?_execution (I : Interchange) [I.Valid] (xs : List I.Word)
    (st : CompensationState I) (r : Result (CompensationState I))
    (hr : compensatedAux? I st xs = some r) :
    compensatedCore I st.high st.correction xs = ⟨(r.value.high,r.value.correction),r.flags⟩ := by
  induction xs generalizing st r with
  | nil => cases Option.some.inj hr; rfl
  | cons a xs ih =>
    unfold compensatedAux? at hr
    cases ht : compensatedStep? I st a with
    | none => simp [ht] at hr
    | some t =>
      cases hout : compensatedAux? I t.value xs with
      | none => simp [ht,hout] at hr
      | some out =>
        have heq : (⟨out.value,Flags.union t.flags out.flags⟩ : Result (CompensationState I)) = r := by
          simpa [ht,hout] using hr
        cases heq
        have hstep := compensatedStep?_execution I st a t ht
        simp only [compensatedCore,Result.bind]
        rw [← hstep.1,← hstep.2.1,ih t.value out hout]
        simp only [hstep.2.2,Flags.union_assoc]

/-- A successful certificate describes exactly the total computation, including flags. -/
theorem compensatedSum?_execution (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : CompensatedCertificate I) (hr : compensatedSum? I xs = some r) :
    compensatedSum I xs = r.result := by
  unfold compensatedSum? at hr
  cases hp : compensatedPass? I xs with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    have he := compensatedAux?_execution I xs (CompensationState.initial I) p hp
    unfold compensatedSum
    change (compensatedCore I (CompensationState.initial I).high
      (CompensationState.initial I).correction xs).bind _ = _
    rw [he]
    rfl

/-- The executable radius bounds the error of the total IEEE computation. -/
theorem compensatedSum_error_of_certificate (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : CompensatedCertificate I) (hr : compensatedSum? I xs = some r) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ (r.errorBound : ℝ) := by
  obtain ⟨q,hq,he,_⟩ := compensatedSum?_sound I xs r hr
  rw [compensatedSum?_execution I xs r hr]
  exact ⟨q,hq,he⟩

/-- A zero radius certifies the exact sum, despite inexact flags in intermediate arithmetic. -/
theorem compensatedSum_exact_of_zero_bound (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : (compensatedSum? I xs).map (fun r => r.errorBound) = some 0) :
    I.decode? (compensatedSum I xs).value = some (wordListSum I xs : ℝ) := by
  cases hr : compensatedSum? I xs with
  | none => simp [hr] at h
  | some r =>
    have hz : r.errorBound = 0 := by simpa [hr] using h
    obtain ⟨q,hq,he⟩ := compensatedSum_error_of_certificate I xs r hr
    rw [hz,Rat.cast_zero] at he
    have heq : q = (wordListSum I xs : ℝ) := by simpa only [abs_nonpos_iff, sub_eq_zero] using he
    simpa [heq] using hq

def compensatedEnclosure? (I : Interchange) [I.Valid] (xs : List I.Word) : Option FP.Range.Interval := do
  let r ← compensatedSum? I xs
  some ⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩

/-- The returned rational interval contains the exact mathematical sum of the inputs. -/
theorem compensatedEnclosure?_sound (I : Interchange) [I.Valid] (xs : List I.Word)
    (J : FP.Range.Interval) (hJ : compensatedEnclosure? I xs = some J) :
    J.Contains (wordListSum I xs : ℝ) := by
  unfold compensatedEnclosure? at hJ
  cases hr : compensatedSum? I xs with
  | none => simp [hr] at hJ
  | some r =>
    have heq : (⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩ : FP.Range.Interval) = J := by
      simpa [hr] using hJ
    cases heq
    obtain ⟨q,hq,hbound,_⟩ := compensatedSum?_sound I xs r hr
    have hd := Datum.toRat?_decode I r.result.value
    rw [hq] at hd
    obtain ⟨v,hv,hvq⟩ := Option.map_eq_some_iff.mp hd
    have hw : (wordRat I r.result.value : ℝ) = q := by rw [wordRat_of_decode I _ v hv]; exact hvq
    simp only [FP.Range.Interval.Contains,Rat.cast_sub,Rat.cast_add,hw]
    constructor <;> linarith [(abs_le.mp hbound).1,(abs_le.mp hbound).2]
end FP.IEEE.Software
