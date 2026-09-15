import FP.IEEE.Software.Exactness
import FP.IEEE.Spec.Scaling

/-! Exact power-of-two scaling and certified normalization of finite inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def mixedScaleB (A D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (n : ℤ) : Result D.Word :=
  let d := Datum.decode A a
  if d.isNaN then ⟨convertNaN A D d, fun e => (e == .invalid) && d.isSignaling⟩
  else if d.isInfinite then Result.pure (Datum.infinity d.fields.negative).encode
  else roundWithMode D mode (d.fields.rationalValue * (2 : ℚ)^n) d.fields.negative

def scaleB (I : Interchange) [I.Valid] (mode : RoundingMode) (a : I.Word) (n : ℤ) : Result I.Word :=
  mixedScaleB I I mode a n

theorem mixedScaleB_spec (A D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (n : ℤ) :
    Spec.ScaleB A D mode a n (mixedScaleB A D mode a n) := by
  unfold Spec.ScaleB mixedScaleB
  dsimp only
  split_ifs
  · exact ⟨convertNaN_spec A D _, by simp, fun e he => by simp [he]⟩
  · simp [Result.pure]
  · have h := roundWithMode_spec D mode ((Datum.decode A a).fields.rationalValue * (2 : ℚ)^n)
      (Datum.decode A a).fields.negative
    rw [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Fields.rationalValue_cast] at h
    change Spec.Rounding D mode (A.value (Datum.decode A a).encode * (2 : ℝ)^n) _ _ at h
    simpa only [Datum.encode_decode] using h

theorem mixedScaleB_finite (A D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (q : ℚ) (n : ℤ) (ha : (Datum.decode A a).toRat? = some q) :
    mixedScaleB A D mode a n = roundWithMode D mode (q * (2 : ℚ)^n) (Datum.decode A a).fields.negative := by
  have hd : ∀ d : Datum A, d.toRat? = some q →
      d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = q := by
    intro d; cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]
  obtain ⟨hn, hi, hv⟩ := hd _ ha
  simp [mixedScaleB, hn, hi, hv]

/-- Moving the exponent preserves the significand when the new exponent fits. -/
theorem representable_scale (F : Format) (m e n : ℤ)
    (hl : F.emin - F.fractionBits ≤ e+n) (hu : e+n ≤ F.emax - F.fractionBits)
    (hm : |(m : ℝ)| < (2 : ℝ)^F.precision) :
    F.Representable (((m : ℝ)*(2 : ℝ)^e) * (2 : ℝ)^n) := by
  refine ⟨m, e+n, hl, hu, hm, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_assoc]

/-- A checkable exactness certificate, including the absence of range events. -/
def exactScale? (I : Interchange) [I.Valid] (mode : RoundingMode) (a : I.Word) (n : ℤ) : Option I.Word :=
  let r := scaleB I mode a n
  if (Datum.decode I a).isFinite && flagsClear r.flags then some r.value else none

/-- Exponent extraction for finite nonzero operands; exceptions are explicit failure.
This is a numerical helper, not the IEEE floating-result logB operation. -/
def finiteExponent? (I : Interchange) (a : I.Word) : Option ℤ := do
  let q ← (Datum.decode I a).toRat?
  if q = 0 then none else some (Int.log 2 |q|)

theorem finiteExponent?_bounds (I : Interchange) (a : I.Word) (q : ℚ) (e : ℤ)
    (ha : (Datum.decode I a).toRat? = some q) (he : finiteExponent? I a = some e) :
    (2 : ℝ)^e ≤ |(q : ℝ)| ∧ |(q : ℝ)| < (2 : ℝ)^(e+1) := by
  simp only [finiteExponent?, ha] at he
  change (if q = 0 then none else some (Int.log 2 |q|)) = some e at he
  split_ifs at he with hz
  · have heq : Int.log 2 |q| = e := Option.some.inj he
    rw [← heq, ← log_abs_cast]
    exact ⟨Int.zpow_log_le_self (by norm_num) (abs_pos.mpr (by exact_mod_cast hz)),
      Int.lt_zpow_succ_log_self (by norm_num) _⟩

/-- Exact rational normalization is available even for subnormal source words. -/
def normalized? (I : Interchange) (a : I.Word) : Option (ℚ × ℤ) := do
  let q ← (Datum.decode I a).toRat?
  if q = 0 then none else
    let e := Int.log 2 |q|
    some (q / (2 : ℚ)^e, e)

theorem normalized?_spec (I : Interchange) (a : I.Word) (q m : ℚ) (e : ℤ)
    (ha : (Datum.decode I a).toRat? = some q) (hm : normalized? I a = some (m,e)) :
    (q : ℝ) = (m : ℝ)*(2 : ℝ)^e ∧ 1 ≤ |(m : ℝ)| ∧ |(m : ℝ)| < 2 := by
  simp only [normalized?, ha] at hm
  change (if q = 0 then none else some (q / (2 : ℚ)^Int.log 2 |q|, Int.log 2 |q|)) = some (m,e) at hm
  split_ifs at hm with hz
  · have hp := Prod.mk.inj (Option.some.inj hm)
    have he : finiteExponent? I a = some e := by
      simp [finiteExponent?, ha, hz, ← hp.2]
    obtain ⟨hl, hu⟩ := finiteExponent?_bounds I a q e ha he
    have hme : (m : ℝ) = (q : ℝ) / (2 : ℝ)^e := by
      rw [← hp.1, hp.2]; push_cast; rfl
    have hpos : (0 : ℝ) < 2^e := by positivity
    rw [hme]
    refine ⟨by field_simp, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos]; simpa using hl
    · rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hu
      simpa [mul_comm] using hu

/-- Exact scaling when a destination representability proof is available. -/
theorem mixedScaleB_exact (A D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (q : ℚ) (n : ℤ) (ha : (Datum.decode A a).toRat? = some q)
    (hq : D.format.Representable ((q : ℝ)*(2 : ℝ)^n)) :
    D.decode? (mixedScaleB A D mode a n).value = some ((q : ℝ)*(2 : ℝ)^n) ∧
      (mixedScaleB A D mode a n).flags = Flags.empty := by
  rw [mixedScaleB_finite A D mode a q n ha]
  have h := roundWithMode_exact D mode (q*(2 : ℚ)^n) (Datum.decode A a).fields.negative
    (by simpa using hq)
  simpa using h

theorem exactScale?_sound (I : Interchange) [I.Valid] (mode : RoundingMode)
    (a b : I.Word) (q : ℚ) (n : ℤ) (ha : (Datum.decode I a).toRat? = some q)
    (hb : exactScale? I mode a n = some b) : I.decode? b = some ((q : ℝ)*(2 : ℝ)^n) := by
  unfold exactScale? at hb
  dsimp only at hb
  split_ifs at hb with hf
  have hboth : (Datum.decode I a).isFinite = true ∧ flagsClear (scaleB I mode a n).flags = true := by
    simpa using hf
  have he := flagsClear_iff _ |>.mp hboth.2
  have hw := Option.some.inj hb
  rw [← hw]
  unfold scaleB at he ⊢
  rw [mixedScaleB_finite I I mode a q n ha] at he ⊢
  simpa using roundWithMode_exact_of_no_flags I mode (q*(2 : ℚ)^n) _ he

/-- A word-valued normalization certificate; exponent extraction rejects zero and nonfinite inputs. -/
def normalizeWord? (I : Interchange) [I.Valid] (a : I.Word) : Option (I.Word × ℤ) := do
  let e ← finiteExponent? I a
  let b ← exactScale? I .nearestEven a (-e)
  some (b,e)

theorem normalizeWord?_sound (I : Interchange) [I.Valid] (a b : I.Word) (q : ℚ) (e : ℤ)
    (ha : (Datum.decode I a).toRat? = some q) (hb : normalizeWord? I a = some (b,e)) :
    ∃ m : ℝ, I.decode? b = some m ∧ (q : ℝ) = m*(2 : ℝ)^e ∧ 1 ≤ |m| ∧ |m| < 2 := by
  unfold normalizeWord? at hb
  cases he : finiteExponent? I a with
  | none => simp [he] at hb
  | some k =>
    cases hw : exactScale? I .nearestEven a (-k) with
    | none => simp [he, hw] at hb
    | some w =>
      have hp : w = b ∧ k = e := by simpa [he, hw] using hb
      rcases hp with ⟨rfl, rfl⟩
      obtain ⟨hl, hu⟩ := finiteExponent?_bounds I a q k ha he
      have hd := exactScale?_sound I .nearestEven a w q (-k) ha hw
      have hk : (0 : ℝ) < 2^k := by positivity
      refine ⟨(q : ℝ)*(2 : ℝ)^(-k), hd, ?_, ?_, ?_⟩
      · rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; simp
      · rw [zpow_neg, ← div_eq_mul_inv, abs_div, abs_of_pos hk, le_div_iff₀ hk]
        simpa using hl
      · rw [zpow_neg, ← div_eq_mul_inv, abs_div, abs_of_pos hk, div_lt_iff₀ hk]
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hu
        simpa [mul_comm] using hu
end FP.IEEE.Software
