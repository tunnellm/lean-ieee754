import FP.IEEE.Software.Exactness
import FP.Range.Interval

/-! Outward-rounded IEEE word intervals. Failure denotes an unavailable finite enclosure. -/
namespace FP.IEEE.Software
open Interchange
abbrev WordInterval (I : Interchange) := I.Word × I.Word

def WordContains (I : Interchange) (p : WordInterval I) (x : ℝ) : Prop :=
  ∃ l h : ℝ, I.decode? p.1 = some l ∧ I.decode? p.2 = some h ∧ l ≤ x ∧ x ≤ h

/-- Produce actual IEEE endpoints with outward rounding and accumulated endpoint flags.
An infinite endpoint yields `none`, never a purported finite certificate. -/
def enclose (I : Interchange) (J : FP.Range.Interval) : Option (Result (WordInterval I)) :=
  let l := roundWithMode I .towardNegative J.lo false
  let h := roundWithMode I .towardPositive J.hi false
  if J.hi < J.lo then none
  else if overflowWithMode I.format .towardNegative J.lo || overflowWithMode I.format .towardPositive J.hi
  then none else some ⟨(l.value, h.value), Flags.union l.flags h.flags⟩

theorem enclose_sound (I : Interchange) [I.Valid] (J : FP.Range.Interval) (r : Result (WordInterval I))
    (hr : enclose I J = some r) (x : ℝ) (hx : J.Contains x) : WordContains I r.value x := by
  unfold enclose at hr
  dsimp only at hr
  split_ifs at hr with hj ho
  · have hf : overflowWithMode I.format .towardNegative J.lo = false ∧
        overflowWithMode I.format .towardPositive J.hi = false := by simpa using ho
    cases Option.some.inj hr
    refine ⟨Spec.roundWithMode I.format .towardNegative (J.lo : ℝ),
      Spec.roundWithMode I.format .towardPositive (J.hi : ℝ), ?_, ?_, ?_, ?_⟩
    · exact (roundWithMode_spec I .towardNegative J.lo false).finite
        (by simpa [← overflowWithMode_spec] using hf.1)
    · exact (roundWithMode_spec I .towardPositive J.hi false).finite
        (by simpa [← overflowWithMode_spec] using hf.2)
    · exact (Spec.roundWithMode_down I.format _).trans hx.1
    · exact hx.2.trans (Spec.roundWithMode_up I.format _)

theorem enclose_value_sound (I : Interchange) [I.Valid] (J : FP.Range.Interval) (p : WordInterval I)
    (hp : (enclose I J).map (fun r => r.value) = some p) (x : ℝ) (hx : J.Contains x) :
    WordContains I p x := by
  cases hr : enclose I J with
  | none => simp [hr] at hp
  | some r =>
    have he : r.value = p := by simpa [hr] using hp
    rw [← he]
    exact enclose_sound I J r hr x hx

/-- These endpoints are optimal: every representable lower/upper bound is enclosed. -/
theorem enclose_tight (I : Interchange) [I.Valid] (J : FP.Range.Interval) (r : Result (WordInterval I))
    (hr : enclose I J = some r) (l h : ℝ)
    (hl : I.format.Representable l) (hh : I.format.Representable h)
    (hlJ : l ≤ (J.lo : ℝ)) (hhJ : (J.hi : ℝ) ≤ h) :
    ∃ a b : ℝ, I.decode? r.value.1 = some a ∧ I.decode? r.value.2 = some b ∧ l ≤ a ∧ b ≤ h := by
  unfold enclose at hr
  dsimp only at hr
  split_ifs at hr with hj ho
  · have hf : overflowWithMode I.format .towardNegative J.lo = false ∧
        overflowWithMode I.format .towardPositive J.hi = false := by simpa using ho
    cases Option.some.inj hr
    exact ⟨_, _, (roundWithMode_spec I .towardNegative J.lo false).finite
      (by simpa [← overflowWithMode_spec] using hf.1),
      (roundWithMode_spec I .towardPositive J.hi false).finite
      (by simpa [← overflowWithMode_spec] using hf.2),
      Spec.roundWithMode_le_down I.format _ _ hl hlJ,
      Spec.roundWithMode_up_le I.format _ _ hh hhJ⟩

/-- Exact decoding for compositional interval arithmetic. -/
def intervalOfWords? (I : Interchange) (p : WordInterval I) : Option FP.Range.Interval := do
  let l ← (Datum.decode I p.1).toRat?
  let h ← (Datum.decode I p.2).toRat?
  if l ≤ h then some ⟨l,h⟩ else none

theorem intervalOfWords?_contains (I : Interchange) [I.Valid] (p : WordInterval I) (J : FP.Range.Interval)
    (hJ : intervalOfWords? I p = some J) (x : ℝ) : J.Contains x ↔ WordContains I p x := by
  unfold intervalOfWords? at hJ
  cases hl : (Datum.decode I p.1).toRat? with
  | none => simp [hl] at hJ
  | some l =>
    cases hh : (Datum.decode I p.2).toRat? with
    | none => simp [hl, hh] at hJ
    | some h =>
      simp only [hl, hh] at hJ
      change (if l ≤ h then some (FP.Range.Interval.mk l h) else none) = some J at hJ
      split_ifs at hJ
      · cases Option.some.inj hJ
        have hdl : I.decode? p.1 = some (l : ℝ) := by rw [← Datum.toRat?_decode, hl]; rfl
        have hdh : I.decode? p.2 = some (h : ℝ) := by rw [← Datum.toRat?_decode, hh]; rfl
        simp [WordContains, hdl, hdh, FP.Range.Interval.Contains]

def intervalAdd (I : Interchange) (p q : WordInterval I) : Option (Result (WordInterval I)) := do
  let a ← intervalOfWords? I p
  let b ← intervalOfWords? I q
  enclose I (a.add b)

def intervalMul (I : Interchange) (p q : WordInterval I) : Option (Result (WordInterval I)) := do
  let a ← intervalOfWords? I p
  let b ← intervalOfWords? I q
  enclose I (a.mul b)

theorem intervalAdd_sound (I : Interchange) [I.Valid] (p q : WordInterval I)
    (r : Result (WordInterval I)) (hr : intervalAdd I p q = some r)
    (x y : ℝ) (hx : WordContains I p x) (hy : WordContains I q y) : WordContains I r.value (x+y) := by
  unfold intervalAdd at hr
  cases ha : intervalOfWords? I p with
  | none => simp [ha] at hr
  | some a =>
    cases hb : intervalOfWords? I q with
    | none => simp [ha, hb] at hr
    | some b =>
      have he : enclose I (a.add b) = some r := by simpa [ha, hb] using hr
      exact enclose_sound I _ r he _ (FP.Range.Interval.contains_add
        ((intervalOfWords?_contains I p a ha x).mpr hx) ((intervalOfWords?_contains I q b hb y).mpr hy))

theorem intervalMul_sound (I : Interchange) [I.Valid] (p q : WordInterval I)
    (r : Result (WordInterval I)) (hr : intervalMul I p q = some r)
    (x y : ℝ) (hx : WordContains I p x) (hy : WordContains I q y) : WordContains I r.value (x*y) := by
  unfold intervalMul at hr
  cases ha : intervalOfWords? I p with
  | none => simp [ha] at hr
  | some a =>
    cases hb : intervalOfWords? I q with
    | none => simp [ha, hb] at hr
    | some b =>
      have he : enclose I (a.mul b) = some r := by simpa [ha, hb] using hr
      exact enclose_sound I _ r he _ (FP.Range.Interval.contains_mul
        ((intervalOfWords?_contains I p a ha x).mpr hx) ((intervalOfWords?_contains I q b hb y).mpr hy))
end FP.IEEE.Software
