import FP.IEEE.Software.Nearest
import FP.IEEE.Spec.RoundingModes

/-! All-mode rational/real refinement, directed lattice extremality, and
unbounded-exponent range-event classification. -/
namespace FP.IEEE.Software

theorem roundInt_cast (mode : RoundingMode) (x : ℚ) :
    roundInt mode x = Spec.roundInteger mode (x : ℝ) := by
  have hf : ⌊(x : ℝ)⌋ = ⌊x⌋ := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast Int.floor_le x
    · exact_mod_cast Int.lt_floor_add_one x
  have hc : ⌈(x : ℝ)⌉ = ⌈x⌉ := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · exact_mod_cast (Int.ceil_eq_iff.mp (rfl : ⌈x⌉ = ⌈x⌉)).1
    · exact_mod_cast Int.le_ceil x
  have hl : (x : ℝ) - (⌊x⌋ : ℤ) < 1 / 2 ↔ x - (⌊x⌋ : ℚ) < 1 / 2 := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := x - (⌊x⌋ : ℚ)) (q := 1 / 2))
  have hh : (1 : ℝ) / 2 < (x : ℝ) - (⌊x⌋ : ℤ) ↔ 1 / 2 < x - (⌊x⌋ : ℚ) := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := 1 / 2) (q := x - (⌊x⌋ : ℚ)))
  cases mode
  · exact roundInt_even_equiv x
  all_goals simp only [roundInt, Spec.roundInteger, hf, hc, hl, hh, Rat.cast_lt_zero]

theorem scaledRound_cast (F : Format) (mode : RoundingMode) (x : ℚ) :
    (scaledRound F mode x : ℝ) = Spec.roundWithMode F mode (x : ℝ) := by
  unfold scaledRound Spec.roundWithMode
  push_cast
  rw [roundInt_cast]
  simp

/-- Greatest point of the selected lattice no greater than the input. -/
theorem scaledRound_down (F : Format) (x : ℚ) :
    scaledRound F .towardNegative x ≤ x ∧
      ∀ k : ℤ, (k : ℚ) * quantum F x ≤ x →
        (k : ℚ) * quantum F x ≤ scaledRound F .towardNegative x := by
  have hp := quantum_pos F x
  obtain ⟨h, hk⟩ := roundInt_down (x / quantum F x)
  constructor
  · exact (le_div_iff₀ hp).mp h
  · intro k hle
    have hi := hk k ((le_div_iff₀ hp).mpr hle)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hp.le

/-- Least point of the selected lattice no less than the input. -/
theorem scaledRound_up (F : Format) (x : ℚ) :
    x ≤ scaledRound F .towardPositive x ∧
      ∀ k : ℤ, x ≤ (k : ℚ) * quantum F x →
        scaledRound F .towardPositive x ≤ (k : ℚ) * quantum F x := by
  have hp := quantum_pos F x
  obtain ⟨h, hk⟩ := roundInt_up (x / quantum F x)
  constructor
  · exact (div_le_iff₀ hp).mp h
  · intro k hle
    have hi := hk k ((div_le_iff₀ hp).mpr hle)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hp.le

theorem scaledRound_zero_direction (F : Format) (x : ℚ) :
    (x < 0 → scaledRound F .towardZero x = scaledRound F .towardPositive x) ∧
    (0 ≤ x → scaledRound F .towardZero x = scaledRound F .towardNegative x) := by
  have hp := quantum_pos F x
  constructor
  · intro h
    unfold scaledRound
    rw [(roundInt_zero_direction _).1 (div_neg_of_neg_of_pos h hp)]
  · intro h
    unfold scaledRound
    rw [(roundInt_zero_direction _).2 (div_nonneg h hp.le)]

def precisionRoundWithMode (F : Format) (mode : RoundingMode) (x : ℚ) : ℚ :=
  let h := (2 : ℚ) ^ (Int.log 2 |x| - F.fractionBits)
  (roundInt mode (x / h) : ℚ) * h

def maxFinite (F : Format) : ℚ :=
  ((2 : ℚ) ^ (F.fractionBits + 1) - 1) * (2 : ℚ) ^ (F.emax - F.fractionBits)

def overflowWithMode (F : Format) (mode : RoundingMode) (x : ℚ) : Bool :=
  decide (maxFinite F < |precisionRoundWithMode F mode x|)

def tinyWithMode (F : Format) (mode : RoundingMode) (x : ℚ) : Bool :=
  decide (0 < |precisionRoundWithMode F mode x| ∧
    |precisionRoundWithMode F mode x| < (2 : ℚ)^F.emin)

@[simp] theorem maxFinite_cast (F : Format) :
    (maxFinite F : ℝ) = F.maxFinite := by simp [maxFinite, Format.maxFinite]

theorem precisionRoundWithMode_cast (F : Format) (mode : RoundingMode) (x : ℚ) :
    (precisionRoundWithMode F mode x : ℝ) = Spec.precisionRoundWithMode F mode (x : ℝ) := by
  unfold precisionRoundWithMode Spec.precisionRoundWithMode
  rw [log_abs_cast]
  dsimp only
  rw [roundInt_cast]
  push_cast
  rfl

theorem overflowWithMode_spec (F : Format) (mode : RoundingMode) (x : ℚ) :
    overflowWithMode F mode x = true ↔ Spec.OverflowWithMode F mode (x : ℝ) := by
  unfold overflowWithMode Spec.OverflowWithMode
  rw [← precisionRoundWithMode_cast, ← maxFinite_cast]
  simpa only [decide_eq_true_eq, Rat.cast_abs] using
    (Rat.cast_lt (K := ℝ) (p := maxFinite F) (q := |precisionRoundWithMode F mode x|)).symm

theorem tinyWithMode_spec (F : Format) (mode : RoundingMode) (x : ℚ) :
    tinyWithMode F mode x = true ↔ Spec.TinyWithMode F mode (x : ℝ) := by
  unfold tinyWithMode Spec.TinyWithMode Format.minNormal
  rw [← precisionRoundWithMode_cast]
  have hlo := Rat.cast_lt (K := ℝ) (p := 0) (q := |precisionRoundWithMode F mode x|)
  have hhi := Rat.cast_lt (K := ℝ) (p := |precisionRoundWithMode F mode x|) (q := (2 : ℚ)^F.emin)
  simpa only [decide_eq_true_eq, Rat.cast_zero, Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat] using
    (and_congr hlo hhi).symm

@[simp] theorem precisionRoundWithMode_even (F : Format) (x : ℚ) :
    precisionRoundWithMode F .nearestEven x = precisionRound F x := rfl

@[simp] theorem tinyWithMode_even (F : Format) (x : ℚ) :
    tinyWithMode F .nearestEven x = tinyAfter F x := rfl

/-- Every supported integer mode changes the input by strictly less than one.
The nearest modes retain their sharper half-unit theorem. -/
theorem roundInt_error_lt_one (mode : RoundingMode) (x : ℚ) :
    |(roundInt mode x : ℚ) - x| < 1 := by
  have hf := Int.floor_le x
  have hfu := Int.lt_floor_add_one x
  have hc := Int.le_ceil x
  have hcl := (Int.ceil_eq_iff.mp (rfl : ⌈x⌉ = ⌈x⌉)).1
  cases mode with
  | nearestEven =>
    have h := roundInt_nearest_error .nearestEven (Or.inl rfl) x
    linarith
  | nearestAway =>
    have h := roundInt_nearest_error .nearestAway (Or.inr rfl) x
    linarith
  | towardNegative =>
    rw [roundInt, abs_lt]; constructor <;> linarith
  | towardPositive =>
    rw [roundInt, abs_lt]; constructor <;> linarith
  | towardZero =>
    unfold roundInt
    split_ifs <;> rw [abs_lt] <;> constructor <;> linarith

theorem scaledRound_error_lt_quantum (F : Format) (mode : RoundingMode) (x : ℚ) :
    |scaledRound F mode x - x| < quantum F x := by
  have hp := quantum_pos F x
  have he := mul_lt_mul_of_pos_right (roundInt_error_lt_one mode (x / quantum F x)) hp
  have hi : |scaledRound F mode x - x| =
      |(roundInt mode (x / quantum F x) : ℚ) - x / quantum F x| * quantum F x := by
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp]
    unfold scaledRound
    congr 1
    field_simp
  rw [hi]
  simpa using he

/-- A mixed bound for all modes, allowing gradual underflow. Nearest modes
also have the sharper half-quantum bound in `scaledRound_nearest_error`. -/
theorem scaledRound_mixed_error (F : Format) (mode : RoundingMode) (x : ℚ) :
    |(scaledRound F mode x : ℝ) - (x : ℝ)| ≤
      (2 * F.unitRoundoff) * |(x : ℝ)| + F.minSubnormal := by
  have he : |(scaledRound F mode x : ℝ) - (x : ℝ)| ≤ F.quantum (x : ℝ) := by
    rw [← quantum_cast]
    exact_mod_cast (scaledRound_error_lt_quantum F mode x).le
  by_cases hx : x = 0
  · subst x
    simp only [scaledRound, zero_div, roundInt_zero, Int.cast_zero, zero_mul,
      Rat.cast_zero, sub_self, abs_zero, mul_zero, zero_add]
    unfold Format.minSubnormal
    positivity
  by_cases hn : F.minNormal ≤ |(x : ℝ)|
  · have hh := F.half_quantum_le_relative hn
    have heta : 0 ≤ F.minSubnormal := by unfold Format.minSubnormal; positivity
    nlinarith
  · have hpos : 0 < |(x : ℝ)| := abs_pos.mpr (by exact_mod_cast hx)
    have hl : Int.log 2 |(x : ℝ)| < F.emin := by
      apply (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hpos).mp
      exact lt_of_not_ge hn
    have hq : F.quantum (x : ℝ) = F.minSubnormal := by
      simp [Format.quantum, Format.quantumExponent, max_eq_left hl.le, Format.minSubnormal]
    rw [hq] at he
    have hu := mul_nonneg F.unitRoundoff_pos.le (abs_nonneg (x : ℝ))
    nlinarith

/-- Every finite representable input is fixed by every mode, including subnormals. -/
theorem scaledRound_exact (F : Format) (mode : RoundingMode) (x : ℚ)
    (hx : F.Representable (x : ℝ)) : scaledRound F mode x = x := by
  have he : scaledRound F .nearestEven x = x := by
    apply Rat.cast_injective (α := ℝ)
    rw [scaledRound_even_cast, F.roundFinite_exact hx]
  have hk : x / quantum F x = (roundInt .nearestEven (x / quantum F x) : ℚ) := by
    apply (div_eq_iff (ne_of_gt (quantum_pos F x))).mpr
    exact he.symm
  unfold scaledRound
  rw [hk, roundInt_intCast]
  exact he

def roundingFlags (F : Format) (mode : RoundingMode) (x : ℚ) : Flags
  | .invalid | .divideByZero => false
  | .overflow => overflowWithMode F mode x
  | .inexact => overflowWithMode F mode x || decide (scaledRound F mode x ≠ x)
  | .underflow => !overflowWithMode F mode x && decide (scaledRound F mode x ≠ x) &&
      tinyWithMode F mode x

theorem roundingFlags_spec (F : Format) (mode : RoundingMode) (x : ℚ) :
    Spec.RoundingFlags F mode (x : ℝ) (roundingFlags F mode x) := by
  have he : scaledRound F mode x ≠ x ↔ Spec.roundWithMode F mode (x : ℝ) ≠ (x : ℝ) := by
    rw [← scaledRound_cast]
    exact not_congr Rat.cast_inj.symm
  constructor
  · rfl
  · rfl
  · exact overflowWithMode_spec F mode x
  · simp [roundingFlags, overflowWithMode_spec, he]
  · simp [roundingFlags, Bool.eq_false_iff, overflowWithMode_spec, he, tinyWithMode_spec,
      and_assoc]

/-- Under default handling, either range flag implies inexact. -/
theorem roundingFlags_range_inexact (F : Format) (mode : RoundingMode) (x : ℚ) :
    ((roundingFlags F mode x) .overflow = true ∨ (roundingFlags F mode x) .underflow = true) →
      (roundingFlags F mode x) .inexact = true := by
  simp only [roundingFlags, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  rintro (h | ⟨⟨_, h⟩, _⟩)
  · exact Or.inl h
  · exact Or.inr h

end FP.IEEE.Software
