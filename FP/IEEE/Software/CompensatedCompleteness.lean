import FP.IEEE.Software.CompensatedExecution
import FP.IEEE.Software.TwoSumExact

/-! Completeness of compensated-summation certificates from execution finiteness. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Only finiteness is required. TwoSum's reconstruction exactness is derived. -/
def CompensatedStepFinite (I : Interchange) [I.Valid] (s c a : I.Word) : Prop :=
  (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true ∧
  (Datum.decode I a).isFinite = true ∧
  (Datum.decode I (twoSumTrace I s a).sum.value).isFinite = true ∧
  (Datum.decode I (twoSumTrace I s a).bvirt.value).isFinite = true ∧
  (Datum.decode I (add I .nearestEven c (twoSum I s a).value.2).value).isFinite = true

/-- Conditions on the actual total execution, independent of certificate checks. -/
def CompensatedPassFinite (I : Interchange) [I.Valid] (s c : I.Word) : List I.Word → Prop
  | [] => (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true
  | a::xs => CompensatedStepFinite I s c a ∧
      CompensatedPassFinite I (twoSum I s a).value.1
        (add I .nearestEven c (twoSum I s a).value.2).value xs

def CompensatedSumFinite (I : Interchange) [I.Valid] (xs : List I.Word) : Prop :=
  CompensatedPassFinite I (Datum.zero false).encode (Datum.zero false).encode xs ∧
    (Datum.decode I (compensatedSum I xs).value).isFinite = true

instance (I : Interchange) [I.Valid] (s c a : I.Word) : Decidable (CompensatedStepFinite I s c a) := by
  unfold CompensatedStepFinite
  infer_instance

instance (I : Interchange) [I.Valid] (s c : I.Word) (xs : List I.Word) :
    Decidable (CompensatedPassFinite I s c xs) := by
  induction xs generalizing s c with
  | nil => unfold CompensatedPassFinite; infer_instance
  | cons a xs ih =>
    unfold CompensatedPassFinite
    letI := ih (twoSum I s a).value.1 (add I .nearestEven c (twoSum I s a).value.2).value
    infer_instance

instance (I : Interchange) [I.Valid] (xs : List I.Word) : Decidable (CompensatedSumFinite I xs) := by
  unfold CompensatedSumFinite
  infer_instance

theorem compensatedStep?_success_iff_finite (I : Interchange) [I.Valid]
    (st : CompensationState I) (a : I.Word) :
    (compensatedStep? I st a).isSome = true ↔ CompensatedStepFinite I st.high st.correction a := by
  unfold compensatedStep?
  cases ht : certifiedTwoSum? I st.high a with
  | none =>
    have hn : ¬ CompensatedStepFinite I st.high st.correction a := by
      intro h
      have hc := (certifiedTwoSum?_success_iff_finite_stages I st.high a).mpr
        ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
      simp [ht] at hc
    simp [hn]
  | some t =>
    have he := certifiedTwoSum?_execution I st.high a t ht
    subst t
    have hf := (certifiedTwoSum?_success_iff_finite_stages I st.high a).mp ht
    simp [CompensatedStepFinite, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]

theorem compensatedStep?_complete (I : Interchange) [I.Valid]
    (st : CompensationState I) (a : I.Word)
    (h : CompensatedStepFinite I st.high st.correction a) :
    ∃ r, compensatedStep? I st a = some r := by
  have hh := (compensatedStep?_success_iff_finite I st a).mpr h
  cases hr : compensatedStep? I st a with
  | none => simp [hr] at hh
  | some r => exact ⟨r,rfl⟩

/-- The empty auxiliary pass does not check its initial state, so these two
initial-finiteness premises are explicit for arbitrary starting accumulators. -/
theorem compensatedAux?_success_iff_finite (I : Interchange) [I.Valid]
    (st : CompensationState I) (xs : List I.Word)
    (hs : (Datum.decode I st.high).isFinite = true)
    (hc : (Datum.decode I st.correction).isFinite = true) :
    (compensatedAux? I st xs).isSome = true ↔ CompensatedPassFinite I st.high st.correction xs := by
  induction xs generalizing st with
  | nil => simp [compensatedAux?, CompensatedPassFinite, hs, hc]
  | cons a xs ih =>
    cases ht : compensatedStep? I st a with
    | none =>
      have hn : ¬ CompensatedStepFinite I st.high st.correction a := by
        intro h
        have hh := (compensatedStep?_success_iff_finite I st a).mpr h
        simp [ht] at hh
      simp [compensatedAux?, ht, CompensatedPassFinite, hn]
    | some t =>
      have hf := (compensatedStep?_success_iff_finite I st a).mp (by simp [ht])
      have he := compensatedStep?_execution I st a t ht
      have hsf : (Datum.decode I t.value.high).isFinite = true := by
        rw [he.1]
        exact hf.2.2.2.1
      have hcf : (Datum.decode I t.value.correction).isFinite = true := by
        rw [he.2.1]
        exact hf.2.2.2.2.2
      have hsome : (compensatedAux? I st (a::xs)).isSome = (compensatedAux? I t.value xs).isSome := by
        simp only [compensatedAux?, ht]
        change ((compensatedAux? I t.value xs).bind
          (fun r => some (⟨r.value,t.flags.union r.flags⟩ : Result (CompensationState I)))).isSome = _
        cases compensatedAux? I t.value xs <;> rfl
      rw [hsome, ih t.value hsf hcf]
      simp only [CompensatedPassFinite, hf, true_and]
      rw [← he.1, ← he.2.1]

theorem compensatedPass?_success_iff_finite (I : Interchange) [I.Valid] (xs : List I.Word) :
    (compensatedPass? I xs).isSome = true ↔
      CompensatedPassFinite I (Datum.zero false).encode (Datum.zero false).encode xs := by
  exact compensatedAux?_success_iff_finite I (CompensationState.initial I) xs (by simp [CompensationState.initial, Datum.isFinite])
    (by simp [CompensationState.initial, Datum.isFinite])

theorem compensatedPass?_complete (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedPassFinite I (Datum.zero false).encode (Datum.zero false).encode xs) :
    ∃ r, compensatedPass? I xs = some r := by
  have hh := (compensatedPass?_success_iff_finite I xs).mpr h
  cases hr : compensatedPass? I xs with
  | none => simp [hr] at hh
  | some r => exact ⟨r,rfl⟩

/-- Full success is equivalent to finite execution, including the final addition. -/
theorem compensatedSum?_success_iff_finite (I : Interchange) [I.Valid] (xs : List I.Word) :
    (compensatedSum? I xs).isSome = true ↔ CompensatedSumFinite I xs := by
  cases hp : compensatedPass? I xs with
  | none =>
    have hn : ¬ CompensatedPassFinite I (Datum.zero false).encode (Datum.zero false).encode xs := by
      intro h
      have hh := (compensatedPass?_success_iff_finite I xs).mpr h
      simp [hp] at hh
    simp [compensatedSum?, hp, CompensatedSumFinite, hn]
  | some p =>
    have hf := (compensatedPass?_success_iff_finite I xs).mp (by simp [hp])
    have he := compensatedAux?_execution I xs (CompensationState.initial I) p hp
    have hv : (compensatedSum I xs).value = (add I .nearestEven p.value.high p.value.correction).value := by
      unfold compensatedSum
      change ((compensatedCore I (CompensationState.initial I).high
        (CompensationState.initial I).correction xs).bind _).value = _
      rw [he]
      rfl
    simp [compensatedSum?, hp, CompensatedSumFinite, hf, hv]

theorem compensatedSum?_complete (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumFinite I xs) : ∃ r, compensatedSum? I xs = some r := by
  have hh := (compensatedSum?_success_iff_finite I xs).mpr h
  cases hr : compensatedSum? I xs with
  | none => simp [hr] at hh
  | some r => exact ⟨r,rfl⟩

/-- Finiteness conditions also supply the existing result/flag equality and radius. -/
theorem compensatedSum_error_radius_of_finite (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumFinite I xs) :
    ∃ r : CompensatedCertificate I, compensatedSum? I xs = some r ∧
      compensatedSum I xs = r.result ∧ ∃ q : ℝ,
      I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ (r.errorBound : ℝ) := by
  obtain ⟨r,hr⟩ := compensatedSum?_complete I xs h
  exact ⟨r,hr,compensatedSum?_execution I xs r hr,compensatedSum_error_of_certificate I xs r hr⟩

theorem compensatedEnclosure?_exists_of_finite (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumFinite I xs) :
    ∃ J, compensatedEnclosure? I xs = some J ∧ J.Contains (wordListSum I xs : ℝ) := by
  obtain ⟨r,hr⟩ := compensatedSum?_complete I xs h
  let J : FP.Range.Interval := ⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩
  have hJ : compensatedEnclosure? I xs = some J := by simp [compensatedEnclosure?, hr, J]
  exact ⟨J,hJ,compensatedEnclosure?_sound I xs J hJ⟩

end FP.IEEE.Software
