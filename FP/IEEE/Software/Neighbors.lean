import FP.IEEE.Software.Exactness

/-! Adjacent IEEE values via exact half-minimum-spacing probes and directed rounding.
No enumeration of the word space or host floating-point operation is used. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def neighborProbe (F : Format) (up : Bool) (q : ℚ) : ℚ :=
  if up then q + (2 : ℚ)^(F.emin - F.fractionBits) / 2
  else q - (2 : ℚ)^(F.emin - F.fractionBits) / 2

def neighborMode (up : Bool) : RoundingMode := if up then .towardPositive else .towardNegative

def next (I : Interchange) [I.Valid] (up : Bool) (a : I.Word) : Result I.Word :=
  let d := Datum.decode I a
  if d.isNaN then ⟨convertNaN I I d, fun e => (e == .invalid) && d.isSignaling⟩
  else if d.isInfinite then
    if d.fields.negative == up then Result.pure (overflowResult I .towardZero d.fields.negative).value
    else Result.pure (Datum.infinity d.fields.negative).encode
  else Result.pure (roundWithMode I (neighborMode up) (neighborProbe I.format up d.fields.rationalValue) false).value

def nextUp (I : Interchange) [I.Valid] (a : I.Word) : Result I.Word := next I true a

def nextDown (I : Interchange) [I.Valid] (a : I.Word) : Result I.Word := next I false a

theorem next_finite (I : Interchange) [I.Valid] (up : Bool) (a : I.Word) (q : ℚ)
    (ha : (Datum.decode I a).toRat? = some q) :
    next I up a = Result.pure (roundWithMode I (neighborMode up) (neighborProbe I.format up q) false).value := by
  have hd : ∀ d : Datum I, d.toRat? = some q →
      d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = q := by
    intro d; cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]
  obtain ⟨hn, hi, hv⟩ := hd _ ha
  simp [next, hn, hi, hv]

theorem neighborProbe_cast (F : Format) (up : Bool) (q : ℚ) :
    (neighborProbe F up q : ℝ) = if up then (q : ℝ)+F.minSubnormal/2 else (q : ℝ)-F.minSubnormal/2 := by
  cases up <;> simp [neighborProbe, Format.minSubnormal]

/-- A finite successor is strictly larger and is the least representable larger value. -/
theorem nextUp_adjacent (I : Interchange) [I.Valid] (a : I.Word) (q : ℚ)
    (ha : (Datum.decode I a).toRat? = some q)
    (ho : overflowWithMode I.format .towardPositive (neighborProbe I.format true q) = false) :
    ∃ y : ℝ, I.decode? (nextUp I a).value = some y ∧ I.format.Representable y ∧
      (q : ℝ) < y ∧ ∀ z : ℝ, I.format.Representable z → (q : ℝ) < z → y ≤ z := by
  have hq := rat_representable_of_decode I a q ha
  have hn : ¬Spec.OverflowWithMode I.format .towardPositive (neighborProbe I.format true q : ℝ) :=
    by simpa [← overflowWithMode_spec] using ho
  rw [nextUp, next_finite I true a q ha]
  refine ⟨Spec.roundWithMode I.format .towardPositive (neighborProbe I.format true q : ℝ),
    (roundWithMode_spec I .towardPositive _ false).finite hn,
    Spec.roundWithMode_representable I.format .towardPositive _ hn, ?_, ?_⟩
  · have h := Spec.roundWithMode_up I.format (neighborProbe I.format true q : ℝ)
    simp [neighborProbe_cast] at h ⊢
    have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
    linarith
  · intro z hz hxz
    apply Spec.roundWithMode_up_le I.format _ z hz
    have hg := representable_gap I.format (q : ℝ) z hq hz hxz
    simp [neighborProbe_cast]
    have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
    linarith

/-- A finite predecessor is strictly smaller and is the greatest representable smaller value. -/
theorem nextDown_adjacent (I : Interchange) [I.Valid] (a : I.Word) (q : ℚ)
    (ha : (Datum.decode I a).toRat? = some q)
    (ho : overflowWithMode I.format .towardNegative (neighborProbe I.format false q) = false) :
    ∃ y : ℝ, I.decode? (nextDown I a).value = some y ∧ I.format.Representable y ∧
      y < (q : ℝ) ∧ ∀ z : ℝ, I.format.Representable z → z < (q : ℝ) → z ≤ y := by
  have hq := rat_representable_of_decode I a q ha
  have hn : ¬Spec.OverflowWithMode I.format .towardNegative (neighborProbe I.format false q : ℝ) :=
    by simpa [← overflowWithMode_spec] using ho
  rw [nextDown, next_finite I false a q ha]
  refine ⟨Spec.roundWithMode I.format .towardNegative (neighborProbe I.format false q : ℝ),
    (roundWithMode_spec I .towardNegative _ false).finite hn,
    Spec.roundWithMode_representable I.format .towardNegative _ hn, ?_, ?_⟩
  · have h := Spec.roundWithMode_down I.format (neighborProbe I.format false q : ℝ)
    simp [neighborProbe_cast] at h ⊢
    have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
    linarith
  · intro z hz hzx
    apply Spec.roundWithMode_le_down I.format _ z hz
    have hg := representable_gap I.format z (q : ℝ) hz hq hzx
    simp [neighborProbe_cast]
    have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
    linarith

/-- Neighbor operations do not raise arithmetic range or inexact flags. -/
theorem next_flags (I : Interchange) [I.Valid] (up : Bool) (a : I.Word) :
    (next I up a).flags .invalid = (Datum.decode I a).isSignaling ∧
    ∀ e, e ≠ .invalid → (next I up a).flags e = false := by
  unfold next
  generalize Datum.decode I a = d
  cases d <;> simp [Datum.isNaN, Datum.isInfinite, Datum.isSignaling, Result.pure, Flags.empty]
  all_goals split_ifs <;> simp [Flags.empty]

/-- Even at the finite/infinite boundary the result is specified without a range assumption. -/
theorem nextUp_finite_spec (I : Interchange) [I.Valid] (a : I.Word) (q : ℚ)
    (ha : (Datum.decode I a).toRat? = some q) :
    (∃ y : ℝ, I.decode? (nextUp I a).value = some y ∧ I.format.Representable y ∧
      (q : ℝ) < y ∧ ∀ z : ℝ, I.format.Representable z → (q : ℝ) < z → y ≤ z) ∨
    (Datum.decode I (nextUp I a).value = .infinity false ∧
      ∀ z : ℝ, I.format.Representable z → z ≤ (q : ℝ)) := by
  by_cases ho : overflowWithMode I.format .towardPositive (neighborProbe I.format true q) = false
  · exact Or.inl (nextUp_adjacent I a q ha ho)
  right
  have hq := rat_representable_of_decode I a q ha
  have hmax := representable_le_max I.format (q : ℝ) hq
  have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  have hb : I.format.maxFinite < (neighborProbe I.format true q : ℝ) := by
    by_contra hh
    have hr : |(neighborProbe I.format true q : ℝ)| ≤ I.format.maxFinite := by
      apply abs_le.mpr
      constructor
      · simp [neighborProbe_cast]; linarith [(abs_le.mp hmax).1]
      · exact le_of_not_gt hh
    have hrat : |neighborProbe I.format true q| ≤ maxFinite I.format := by
      rw [← maxFinite_cast] at hr; exact_mod_cast hr
    exact ho (noOverflow_of_abs_le_max I.format .towardPositive _ hrat)
  have hpos : 0 < (neighborProbe I.format true q : ℝ) := by
    have hm : 0 < I.format.maxFinite := by rw [← maxFinite_cast]; exact_mod_cast maxFinite_pos I.format
    exact hm.trans hb
  constructor
  · rw [nextUp, next_finite I true a q ha]
    have hs := (roundWithMode_spec I .towardPositive (neighborProbe I.format true q) false).overflow_infinite
      ((overflowWithMode_spec _ _ _).mp (Bool.eq_true_of_not_eq_false ho))
    have hsign : Spec.realSign (neighborProbe I.format true q : ℝ) false = false := by
      simp [Spec.realSign, ne_of_gt hpos, not_lt.mpr hpos.le]
    simpa [hsign, Result.pure, neighborMode] using hs (by simp [Spec.OverflowToInfinity, hsign])
  · intro z hz
    by_contra hh
    have hg := representable_gap I.format (q : ℝ) z hq hz (lt_of_not_ge hh)
    have hm := (le_abs_self z).trans (representable_le_max I.format z hz)
    simp [neighborProbe_cast] at hb
    linarith

theorem nextDown_finite_spec (I : Interchange) [I.Valid] (a : I.Word) (q : ℚ)
    (ha : (Datum.decode I a).toRat? = some q) :
    (∃ y : ℝ, I.decode? (nextDown I a).value = some y ∧ I.format.Representable y ∧
      y < (q : ℝ) ∧ ∀ z : ℝ, I.format.Representable z → z < (q : ℝ) → z ≤ y) ∨
    (Datum.decode I (nextDown I a).value = .infinity true ∧
      ∀ z : ℝ, I.format.Representable z → (q : ℝ) ≤ z) := by
  by_cases ho : overflowWithMode I.format .towardNegative (neighborProbe I.format false q) = false
  · exact Or.inl (nextDown_adjacent I a q ha ho)
  right
  have hq := rat_representable_of_decode I a q ha
  have hmax := representable_le_max I.format (q : ℝ) hq
  have hp : 0 < I.format.minSubnormal := by unfold Format.minSubnormal; positivity
  have hb : (neighborProbe I.format false q : ℝ) < -I.format.maxFinite := by
    by_contra hh
    have hr : |(neighborProbe I.format false q : ℝ)| ≤ I.format.maxFinite := by
      apply abs_le.mpr
      constructor
      · exact le_of_not_gt hh
      · simp [neighborProbe_cast]; linarith [(abs_le.mp hmax).2]
    have hrat : |neighborProbe I.format false q| ≤ maxFinite I.format := by
      rw [← maxFinite_cast] at hr; exact_mod_cast hr
    exact ho (noOverflow_of_abs_le_max I.format .towardNegative _ hrat)
  have hneg : (neighborProbe I.format false q : ℝ) < 0 := by
    have hm : 0 < I.format.maxFinite := by rw [← maxFinite_cast]; exact_mod_cast maxFinite_pos I.format
    linarith
  constructor
  · rw [nextDown, next_finite I false a q ha]
    have hs := (roundWithMode_spec I .towardNegative (neighborProbe I.format false q) false).overflow_infinite
      ((overflowWithMode_spec _ _ _).mp (Bool.eq_true_of_not_eq_false ho))
    have hsign : Spec.realSign (neighborProbe I.format false q : ℝ) false = true := by
      simp [Spec.realSign, ne_of_lt hneg, hneg]
    simpa [hsign, Result.pure, neighborMode] using hs (by simp [Spec.OverflowToInfinity, hsign])
  · intro z hz
    by_contra hh
    have hg := representable_gap I.format z (q : ℝ) hz hq (lt_of_not_ge hh)
    have hm := (abs_le.mp (representable_le_max I.format z hz)).1
    simp [neighborProbe_cast] at hb
    linarith

theorem next_nan (I : Interchange) [I.Valid] (up : Bool) (a : I.Word)
    (hn : (Datum.decode I a).isNaN = true) :
    Spec.ConvertedNaN I I (Datum.decode I a) (next I up a).value := by
  simpa [next, hn] using convertNaN_spec I I (Datum.decode I a)

/-- Inward infinity steps reach signed maxFinite; outward steps preserve infinity. -/
theorem next_infinity (I : Interchange) [I.Valid] (up sign : Bool) :
    (if sign == up then I.decode? (next I up (Datum.infinity sign).encode).value =
        some (if sign then -I.format.maxFinite else I.format.maxFinite)
     else Datum.decode I (next I up (Datum.infinity sign).encode).value = .infinity sign) := by
  simp only [next, Datum.decode_encode, Datum.isNaN, Bool.false_eq_true, if_false,
    Datum.isInfinite, if_true, Datum.fields]
  by_cases h : (sign == up) = true
  · simp only [h, if_true, Result.pure]
    exact (overflowResult_spec I .towardZero sign).2.1 (by simp [Spec.OverflowToInfinity])
  · simp [h, Result.pure]
end FP.IEEE.Software
