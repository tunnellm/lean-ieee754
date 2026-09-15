import FP.IEEE.Spec.RoundingModes
import FP.IEEE.Representation

/-! Finite representability under the IEEE unbounded-exponent overflow test. -/
namespace FP.IEEE.Spec
noncomputable section


@[simp] theorem roundInteger_intCast (mode : RoundingMode) (k : ℤ) :
    roundInteger mode (k : ℝ) = k := by
  cases mode <;> simp [roundInteger, roundEven]

@[simp] theorem roundInteger_zero (mode : RoundingMode) : roundInteger mode 0 = 0 := by
  simpa using roundInteger_intCast mode 0

theorem roundInteger_nearest_error (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : ℝ) :
    |(roundInteger mode x : ℝ) - x| ≤ 1 / 2 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  have hm0 : (0 : ℝ) ≤ (⌊x⌋ % 2 : ℤ) := by
    exact_mod_cast Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
  have hm1 : ((⌊x⌋ % 2 : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast (show ⌊x⌋ % 2 ≤ 1 by omega)
  rcases hm with rfl | rfl <;> unfold roundInteger <;> dsimp only [roundEven] <;>
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

theorem roundInteger_error_lt_one (mode : RoundingMode) (x : ℝ) :
    |(roundInteger mode x : ℝ) - x| < 1 := by
  have hf := Int.floor_le x
  have hfu := Int.lt_floor_add_one x
  have hc := Int.le_ceil x
  have hcl := (Int.ceil_eq_iff.mp (rfl : ⌈x⌉ = ⌈x⌉)).1
  cases mode with
  | nearestEven =>
    have h := roundInteger_nearest_error .nearestEven (Or.inl rfl) x
    linarith
  | nearestAway =>
    have h := roundInteger_nearest_error .nearestAway (Or.inr rfl) x
    linarith
  | towardNegative =>
    rw [roundInteger, abs_lt]; constructor <;> linarith
  | towardPositive =>
    rw [roundInteger, abs_lt]; constructor <;> linarith
  | towardZero =>
    unfold roundInteger
    split_ifs <;> rw [abs_lt] <;> constructor <;> linarith

theorem roundInteger_abs_le (mode : RoundingMode) (x : ℝ) (n : ℕ)
    (hx : |x| < (n : ℝ)) : |roundInteger mode x| ≤ (n : ℤ) := by
  have he := roundInteger_error_lt_one mode x
  have ht := abs_add_le ((roundInteger mode x : ℝ) - x) x
  rw [sub_add_cancel] at ht
  have hh : |(roundInteger mode x : ℝ)| < (n : ℝ) + 1 := by linarith
  have hi : |roundInteger mode x| < (n : ℤ) + 1 := by exact_mod_cast hh
  omega

theorem roundInteger_abs_ge (mode : RoundingMode) (x : ℝ) (n : ℕ)
    (hx : (n : ℝ) ≤ |x|) : (n : ℤ) ≤ |roundInteger mode x| := by
  have he := roundInteger_error_lt_one mode x
  have ht := abs_add_le (x - (roundInteger mode x : ℝ)) (roundInteger mode x : ℝ)
  rw [sub_add_cancel, abs_sub_comm] at ht
  have hh : (n : ℝ) < |(roundInteger mode x : ℝ)| + 1 := by linarith
  have hi : (n : ℤ) < |roundInteger mode x| + 1 := by exact_mod_cast hh
  omega

private theorem precision_scale (F : Format) (x : ℝ) :
    (2 : ℝ)^F.fractionBits * (2 : ℝ)^(Int.log 2 |x| - F.fractionBits) =
      (2 : ℝ)^Int.log 2 |x| := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem precisionRound_abs_lower (F : Format) (mode : RoundingMode) (x : ℝ) (hx : x ≠ 0) :
    (2 : ℝ)^Int.log 2 |x| ≤ |precisionRoundWithMode F mode x| := by
  let h := (2 : ℝ)^(Int.log 2 |x| - F.fractionBits)
  have hp : 0 < h := by dsimp [h]; positivity
  have hs : (2 : ℝ)^F.fractionBits * h = (2 : ℝ)^Int.log 2 |x| := precision_scale F x
  have hi : (2 : ℝ)^F.fractionBits ≤ |x / h| := by
    rw [abs_div, abs_of_pos hp, le_div_iff₀ hp, hs]
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
  have hm := roundInteger_abs_ge mode (x / h) (2^F.fractionBits) (by exact_mod_cast hi)
  have hr : (2 : ℝ)^F.fractionBits ≤ |(roundInteger mode (x / h) : ℝ)| := by exact_mod_cast hm
  change _ ≤ |(roundInteger mode (x / h) : ℝ) * h|
  rw [abs_mul, abs_of_pos hp, ← hs]
  exact mul_le_mul_of_nonneg_right hr hp.le

theorem maxFinite_lt_next (F : Format) : F.maxFinite < (2 : ℝ)^(F.emax + 1) := by
  have he : (2 : ℝ)^(F.fractionBits + 1) * (2 : ℝ)^(F.emax - F.fractionBits) =
      (2 : ℝ)^(F.emax + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  rw [← he]
  unfold Format.maxFinite
  exact mul_lt_mul_of_pos_right (by linarith) (by positivity)

theorem log_le_of_noOverflow (F : Format) (mode : RoundingMode) (x : ℝ)
    (hx : x ≠ 0) (ho : ¬ OverflowWithMode F mode x) : Int.log 2 |x| ≤ F.emax := by
  have hb : |precisionRoundWithMode F mode x| ≤ F.maxFinite := by
    simpa [OverflowWithMode, not_lt] using ho
  have hl := precisionRound_abs_lower F mode x hx
  have hu := maxFinite_lt_next F
  by_contra h
  have hh : (2 : ℝ)^(F.emax + 1) ≤ (2 : ℝ)^Int.log 2 |x| :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

theorem roundWithMode_representable (F : Format) (mode : RoundingMode) (x : ℝ)
    (ho : ¬ OverflowWithMode F mode x) : F.Representable (roundWithMode F mode x : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simpa [roundWithMode] using F.representable_zero
  let m := roundInteger mode (x / F.quantum x)
  let e := F.quantumExponent x
  have hel : F.emin - F.fractionBits ≤ e := by dsimp [e, Format.quantumExponent]; omega
  have heu : e ≤ F.emax - F.fractionBits := by
    have hl := log_le_of_noOverflow F mode x hx ho
    have hf := F.exponent_order
    dsimp [e, Format.quantumExponent]
    omega
  have hi : |x / F.quantum x| < (2 : ℝ)^F.precision := by
    exact F.scaled_lt_precision x
  have hmi := roundInteger_abs_le mode (x / F.quantum x) (2^F.precision) (by exact_mod_cast hi)
  have hm : |(m : ℝ)| ≤ (2 : ℝ)^F.precision := by exact_mod_cast hmi
  have hv : (roundWithMode F mode x : ℝ) = (m : ℝ) * (2 : ℝ)^e := by
    rfl
  rcases hm.lt_or_eq with hlt | heq
  · exact ⟨m, e, hel, heu, hlt, hv⟩
  have hstrict : e < F.emax - F.fractionBits := by
    by_contra hh
    have he : e = F.emax - F.fractionBits := by omega
    by_cases hn : F.emin ≤ Int.log 2 |x|
    · have hp : precisionRoundWithMode F mode x = roundWithMode F mode x := by
        simp [precisionRoundWithMode, roundWithMode, Format.quantum, Format.quantumExponent, max_eq_right hn]
      have hb : |precisionRoundWithMode F mode x| ≤ F.maxFinite := by simpa [OverflowWithMode, not_lt] using ho
      rw [hp] at hb
      have hbR := hb
      rw [hv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^e), heq, he] at hbR
      unfold Format.maxFinite Format.precision at hbR
      have hz : (0 : ℝ) < 2^(F.emax - F.fractionBits) := by positivity
      nlinarith
    · have hq : F.quantum x = (2 : ℝ)^(F.emin - F.fractionBits) := by
        simp [Format.quantum, Format.quantumExponent, max_eq_left (le_of_not_ge hn)]
      have hl : |x| < (2 : ℝ)^F.emin :=
        (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hx)).mpr (lt_of_not_ge hn)
      have hs : (2 : ℝ)^F.fractionBits * F.quantum x = (2 : ℝ)^F.emin := by
        rw [hq, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        omega
      have hi' : |x / F.quantum x| < (2 : ℝ)^F.fractionBits := by
        rw [abs_div, abs_of_pos (F.quantum_pos x), div_lt_iff₀ (F.quantum_pos x), hs]
        exact hl
      have hh := roundInteger_abs_le mode (x / F.quantum x) (2^F.fractionBits) (by exact_mod_cast hi')
      have hhR : |(m : ℝ)| ≤ (2 : ℝ)^F.fractionBits := by exact_mod_cast hh
      rw [heq, Format.precision, pow_succ] at hhR
      have hz : (0 : ℝ) < 2^F.fractionBits := by positivity
      nlinarith
  have hpow : (2 : ℝ)^F.precision * (2 : ℝ)^e =
      (2 : ℝ)^F.fractionBits * (2 : ℝ)^(e + 1) := by
    simp [Format.precision, pow_succ, zpow_add₀]
    ring
  have hlt : (2 : ℝ)^F.fractionBits < (2 : ℝ)^F.precision := by
    rw [Format.precision, pow_succ]
    have hz : (0 : ℝ) < 2^F.fractionBits := by positivity
    linarith
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ 2^F.precision)).mp heq with hmpos | hmneg
  · refine ⟨(2 : ℤ)^F.fractionBits, e + 1, by omega, by omega, by simpa using hlt, ?_⟩
    rw [hv, hmpos]
    simpa using hpow
  · refine ⟨-((2 : ℤ)^F.fractionBits), e + 1, by omega, by omega, by simpa using hlt, ?_⟩
    rw [hv, hmneg]
    push_cast
    nlinarith [hpow]

theorem roundWithMode_error_lt_quantum (F : Format) (mode : RoundingMode) (x : ℝ) :
    |roundWithMode F mode x - x| < F.quantum x := by
  have hp := F.quantum_pos x
  have he := mul_lt_mul_of_pos_right (roundInteger_error_lt_one mode (x / F.quantum x)) hp
  have hi : |roundWithMode F mode x - x| =
      |(roundInteger mode (x / F.quantum x) : ℝ) - x / F.quantum x| * F.quantum x := by
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp]
    unfold roundWithMode
    congr 1
    field_simp
  rw [hi]
  simpa using he

/-- A mixed bound for all modes, allowing gradual underflow. Nearest modes
also have the sharper half-quantum bound in `roundWithMode_nearest_error`. -/
theorem roundWithMode_mixed_error (F : Format) (mode : RoundingMode) (x : ℝ) :
    |(roundWithMode F mode x : ℝ) - (x : ℝ)| ≤
      (2 * F.unitRoundoff) * |(x : ℝ)| + F.minSubnormal := by
  have he : |(roundWithMode F mode x : ℝ) - (x : ℝ)| ≤ F.quantum (x : ℝ) := by
    exact (roundWithMode_error_lt_quantum F mode x).le
  by_cases hx : x = 0
  · subst x
    simp only [roundWithMode, zero_div, roundInteger_zero, Int.cast_zero, zero_mul,
      sub_self, abs_zero, mul_zero, zero_add]
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


end
end FP.IEEE.Spec
