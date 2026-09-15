import FP.IEEE.Software.CompensatedDotCertificate

/-! Completeness from the actual finite Dot2 execution, without exact-product certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def CompensatedDotPassFinite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : ℕ → Prop
  | 0 => True
  | n+1 => CompensatedDotPassFinite I a b n ∧
      CompensatedDotStepFinite I (compensatedDotCore I a b n).value.1
        (compensatedDotCore I a b n).value.2 (a n) (b n)

def CompensatedDotFinite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Prop :=
  CompensatedDotPassFinite I a b n ∧ (Datum.decode I (compensatedDot I a b n).value).isFinite = true

instance (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Decidable (CompensatedDotPassFinite I a b n) := by
  induction n with
  | zero => unfold CompensatedDotPassFinite; infer_instance
  | succ n ih => unfold CompensatedDotPassFinite; letI := ih; infer_instance

instance (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Decidable (CompensatedDotFinite I a b n) := by
  unfold CompensatedDotFinite; infer_instance

theorem compensatedDotPass?_success_iff_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) :
    (compensatedDotPass? I a b n).isSome = true ↔ CompensatedDotPassFinite I a b n := by
  induction n with
  | zero => simp [compensatedDotPass?,CompensatedDotPassFinite]
  | succ n ih =>
    cases hp : compensatedDotPass? I a b n with
    | none =>
      have hf : ¬ CompensatedDotPassFinite I a b n := by simpa [hp] using ih.symm
      simp [compensatedDotPass?,hp,CompensatedDotPassFinite,hf]
    | some p =>
      have hf : CompensatedDotPassFinite I a b n := ih.mp (by simp [hp])
      have he := compensatedDotPass?_execution I a b n p hp
      have hv : (compensatedDotPass? I a b (n+1)).isSome = (compensatedDotStep? I p.value (a n) (b n)).isSome := by
        simp only [compensatedDotPass?,hp]
        change ((compensatedDotStep? I p.value (a n) (b n)).bind
          (fun r => some (⟨r.value,p.flags.union r.flags⟩ : Result (DotCompensationState I)))).isSome = _
        cases compensatedDotStep? I p.value (a n) (b n) <;> rfl
      rw [hv,compensatedDotStep?_success_iff_finite]
      simp [CompensatedDotPassFinite,hf,he]

theorem compensatedDot?_success_iff_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) :
    (compensatedDot? I a b n).isSome = true ↔ CompensatedDotFinite I a b n := by
  cases hp : compensatedDotPass? I a b n with
  | none =>
    have hf : ¬ CompensatedDotPassFinite I a b n := by
      simpa [hp] using (compensatedDotPass?_success_iff_finite I a b n).symm
    simp [compensatedDot?,hp,CompensatedDotFinite,hf]
  | some p =>
    have hf := (compensatedDotPass?_success_iff_finite I a b n).mp (by simp [hp])
    have he := compensatedDotPass?_execution I a b n p hp
    simp [compensatedDot?,hp,CompensatedDotFinite,hf,compensatedDot,he,Result.bind]

theorem compensatedDot?_complete (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotFinite I a b n) : ∃ r, compensatedDot? I a b n = some r := by
  have hh := (compensatedDot?_success_iff_finite I a b n).mpr h
  cases hr : compensatedDot? I a b n with
  | none => simp [hr] at hh
  | some r => exact ⟨r,rfl⟩

theorem CompensatedDotPassFinite.result_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotPassFinite I a b n) :
    (Datum.decode I (compensatedDotCore I a b n).value.1).isFinite = true ∧
    (Datum.decode I (compensatedDotCore I a b n).value.2).isFinite = true := by
  cases n with
  | zero => simp [compensatedDotCore,Result.pure,Datum.isFinite]
  | succ n => exact ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2⟩

end FP.IEEE.Software
