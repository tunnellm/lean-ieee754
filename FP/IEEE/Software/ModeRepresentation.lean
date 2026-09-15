import FP.IEEE.Software.Overflow

/-! Finite representability under the IEEE unbounded-exponent overflow test. -/
namespace FP.IEEE.Software

theorem roundInt_abs_le (mode : RoundingMode) (x : ℚ) (n : ℕ)
    (hx : |x| < (n : ℚ)) : |roundInt mode x| ≤ (n : ℤ) := by
  have he := roundInt_error_lt_one mode x
  have ht := abs_add_le ((roundInt mode x : ℚ) - x) x
  rw [sub_add_cancel] at ht
  have hh : |(roundInt mode x : ℚ)| < (n : ℚ) + 1 := by linarith
  have hi : |roundInt mode x| < (n : ℤ) + 1 := by exact_mod_cast hh
  omega

theorem roundInt_abs_ge (mode : RoundingMode) (x : ℚ) (n : ℕ)
    (hx : (n : ℚ) ≤ |x|) : (n : ℤ) ≤ |roundInt mode x| := by
  have he := roundInt_error_lt_one mode x
  have ht := abs_add_le (x - (roundInt mode x : ℚ)) (roundInt mode x : ℚ)
  rw [sub_add_cancel, abs_sub_comm] at ht
  have hh : (n : ℚ) < |(roundInt mode x : ℚ)| + 1 := by linarith
  have hi : (n : ℤ) < |roundInt mode x| + 1 := by exact_mod_cast hh
  omega

private theorem precision_scale (F : Format) (x : ℚ) :
    (2 : ℚ)^F.fractionBits * (2 : ℚ)^(Int.log 2 |x| - F.fractionBits) =
      (2 : ℚ)^Int.log 2 |x| := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  omega

theorem precisionRound_abs_lower (F : Format) (mode : RoundingMode) (x : ℚ) (hx : x ≠ 0) :
    (2 : ℚ)^Int.log 2 |x| ≤ |precisionRoundWithMode F mode x| := by
  let h := (2 : ℚ)^(Int.log 2 |x| - F.fractionBits)
  have hp : 0 < h := by dsimp [h]; positivity
  have hs : (2 : ℚ)^F.fractionBits * h = (2 : ℚ)^Int.log 2 |x| := precision_scale F x
  have hi : (2 : ℚ)^F.fractionBits ≤ |x / h| := by
    rw [abs_div, abs_of_pos hp, le_div_iff₀ hp, hs]
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
  have hm := roundInt_abs_ge mode (x / h) (2^F.fractionBits) (by exact_mod_cast hi)
  have hr : (2 : ℚ)^F.fractionBits ≤ |(roundInt mode (x / h) : ℚ)| := by exact_mod_cast hm
  change _ ≤ |(roundInt mode (x / h) : ℚ) * h|
  rw [abs_mul, abs_of_pos hp, ← hs]
  exact mul_le_mul_of_nonneg_right hr hp.le

theorem maxFinite_lt_next (F : Format) : maxFinite F < (2 : ℚ)^(F.emax + 1) := by
  have he : (2 : ℚ)^(F.fractionBits + 1) * (2 : ℚ)^(F.emax - F.fractionBits) =
      (2 : ℚ)^(F.emax + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    push_cast
    ring
  rw [← he]
  unfold maxFinite
  exact mul_lt_mul_of_pos_right (by linarith) (by positivity)

theorem log_le_of_noOverflow (F : Format) (mode : RoundingMode) (x : ℚ)
    (hx : x ≠ 0) (ho : overflowWithMode F mode x = false) : Int.log 2 |x| ≤ F.emax := by
  have hb : |precisionRoundWithMode F mode x| ≤ maxFinite F := by
    simpa [overflowWithMode] using ho
  have hl := precisionRound_abs_lower F mode x hx
  have hu := maxFinite_lt_next F
  by_contra h
  have hh : (2 : ℚ)^(F.emax + 1) ≤ (2 : ℚ)^Int.log 2 |x| :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

theorem scaledRound_representable (F : Format) (mode : RoundingMode) (x : ℚ)
    (ho : overflowWithMode F mode x = false) : F.Representable (scaledRound F mode x : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simpa [scaledRound] using F.representable_zero
  let m := roundInt mode (x / quantum F x)
  let e := quantumExponent F x
  have hel : F.emin - F.fractionBits ≤ e := by dsimp [e, quantumExponent]; omega
  have heu : e ≤ F.emax - F.fractionBits := by
    have hl := log_le_of_noOverflow F mode x hx ho
    have hf := F.exponent_order
    dsimp [e, quantumExponent]
    omega
  have hi : |x / quantum F x| < (2 : ℚ)^F.precision := by
    have hr := F.scaled_lt_precision (x : ℝ)
    rw [← quantum_cast] at hr
    exact_mod_cast hr
  have hmi := roundInt_abs_le mode (x / quantum F x) (2^F.precision) (by exact_mod_cast hi)
  have hm : |(m : ℝ)| ≤ (2 : ℝ)^F.precision := by exact_mod_cast hmi
  have hv : (scaledRound F mode x : ℝ) = (m : ℝ) * (2 : ℝ)^e := by
    simp only [scaledRound, quantum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow, Rat.cast_ofNat, m, e]
  rcases hm.lt_or_eq with hlt | heq
  · exact ⟨m, e, hel, heu, hlt, hv⟩
  have hstrict : e < F.emax - F.fractionBits := by
    by_contra hh
    have he : e = F.emax - F.fractionBits := by omega
    by_cases hn : F.emin ≤ Int.log 2 |x|
    · have hp : precisionRoundWithMode F mode x = scaledRound F mode x := by
        simp [precisionRoundWithMode, scaledRound, quantum, quantumExponent, max_eq_right hn]
      have hb : |precisionRoundWithMode F mode x| ≤ maxFinite F := by simpa [overflowWithMode] using ho
      rw [hp] at hb
      have hbR : |(scaledRound F mode x : ℝ)| ≤ F.maxFinite := by
        rw [← maxFinite_cast]
        exact_mod_cast hb
      rw [hv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^e), heq, he] at hbR
      unfold Format.maxFinite Format.precision at hbR
      have hz : (0 : ℝ) < 2^(F.emax - F.fractionBits) := by positivity
      nlinarith
    · have hq : quantum F x = (2 : ℚ)^(F.emin - F.fractionBits) := by
        simp [quantum, quantumExponent, max_eq_left (le_of_not_ge hn)]
      have hl : |x| < (2 : ℚ)^F.emin :=
        (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hx)).mpr (lt_of_not_ge hn)
      have hs : (2 : ℚ)^F.fractionBits * quantum F x = (2 : ℚ)^F.emin := by
        rw [hq, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1
        omega
      have hi' : |x / quantum F x| < (2 : ℚ)^F.fractionBits := by
        rw [abs_div, abs_of_pos (quantum_pos F x), div_lt_iff₀ (quantum_pos F x), hs]
        exact hl
      have hh := roundInt_abs_le mode (x / quantum F x) (2^F.fractionBits) (by exact_mod_cast hi')
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

end FP.IEEE.Software
