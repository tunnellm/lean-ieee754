import FP.IEEE.Format

/-! Range and representability of the exact IEEE rounding function. -/
noncomputable section
namespace FP.IEEE.Format

private theorem pow_precision (F : Format) :
    (2 : ℝ) ^ F.precision = (2 : ℝ) ^ ((F.fractionBits : ℤ) + 1) := by
  simp [precision, pow_succ, zpow_add₀]

private theorem quantum_times_precision (F : Format) (x : ℝ) :
    F.quantum x * (2 : ℝ) ^ F.precision =
      (2 : ℝ) ^ (max F.emin (Int.log 2 |x|) + 1) := by
  rw [pow_precision, quantum, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  unfold quantumExponent
  omega

theorem scaled_lt_precision (F : Format) (x : ℝ) :
    |x / F.quantum x| < (2 : ℝ) ^ F.precision := by
  rw [abs_div, abs_of_pos (F.quantum_pos x), div_lt_iff₀ (F.quantum_pos x)]
  rw [mul_comm, quantum_times_precision]
  exact (Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) |x|).trans_le
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))

theorem rounded_mantissa_le (F : Format) (x : ℝ) :
    |(roundEven (x / F.quantum x) : ℝ)| ≤ (2 : ℝ) ^ F.precision := by
  have he := roundEven_error (x / F.quantum x)
  have hx := F.scaled_lt_precision x
  have ht := abs_add_le ((roundEven (x / F.quantum x) : ℝ) - x / F.quantum x)
    (x / F.quantum x)
  have hb : |(roundEven (x / F.quantum x) : ℝ)| < (2 : ℝ) ^ F.precision + 1 := by
    simp only [sub_add_cancel] at ht
    linarith
  have hi : |roundEven (x / F.quantum x)| < (2 : ℤ) ^ F.precision + 1 := by
    exact_mod_cast hb
  exact_mod_cast (show |roundEven (x / F.quantum x)| ≤ (2 : ℤ) ^ F.precision by omega)

theorem quantumExponent_le_of_noOverflow (F : Format) {x : ℝ}
    (hx : |x| < F.overflowThreshold) (hne : x ≠ 0) :
    F.quantumExponent x ≤ F.emax - F.fractionBits := by
  have ht : F.overflowThreshold < (2 : ℝ) ^ (F.emax + 1) := by
    have he : (2 : ℝ) ^ (F.fractionBits + 1) * (2 : ℝ) ^ (F.emax - F.fractionBits) =
        (2 : ℝ) ^ (F.emax + 1) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    unfold overflowThreshold
    rw [← he]
    have hp : 0 < (2 : ℝ) ^ (F.emax - F.fractionBits) := by positivity
    nlinarith
  have hl : Int.log 2 |x| < F.emax + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) (abs_pos.mpr hne)).mp (hx.trans ht)
  unfold quantumExponent
  have := F.exponent_order
  omega

theorem representable_zero (F : Format) : F.Representable 0 := by
  refine ⟨0, F.emin - F.fractionBits, le_rfl, sub_le_sub_right F.exponent_order _, ?_, ?_⟩
  · simp only [Int.cast_zero, abs_zero]
    positivity
  · simp

/-- Every nonoverflowing rounded result belongs to the finite binary format,
including carry into a new binade and gradual underflow. -/
theorem roundFinite_representable (F : Format) {x : ℝ}
    (hx : |x| < F.overflowThreshold) : F.Representable (F.roundFinite x) := by
  by_cases hz : x = 0
  · subst x
    simpa using F.representable_zero
  let m : ℤ := roundEven (x / F.quantum x)
  let e : ℤ := F.quantumExponent x
  have hel : F.emin - F.fractionBits ≤ e := by
    dsimp [e, quantumExponent]
    omega
  have heu : e ≤ F.emax - F.fractionBits := F.quantumExponent_le_of_noOverflow hx hz
  have hm : |(m : ℝ)| ≤ (2 : ℝ) ^ F.precision := F.rounded_mantissa_le x
  rcases hm.lt_or_eq with hlt | heq
  · exact ⟨m, e, hel, heu, hlt, rfl⟩
  · have hstrict : e < F.emax - F.fractionBits := by
      by_contra hh
      have he : e = F.emax - F.fractionBits := by omega
      have hq : F.quantum x = (2 : ℝ) ^ (F.emax - F.fractionBits) := by
        change (2 : ℝ) ^ e = _
        rw [he]
      have herr := F.roundFinite_abs_error x
      have ha := abs_add_le (F.roundFinite x - x) x
      have hv : |F.roundFinite x| = (2 : ℝ) ^ F.precision * F.quantum x := by
        change |(m : ℝ) * F.quantum x| = _
        rw [abs_mul, abs_of_pos (F.quantum_pos x), heq]
      simp only [sub_add_cancel] at ha
      rw [hv, hq] at ha
      rw [hq] at herr
      unfold overflowThreshold at hx
      unfold precision at ha
      nlinarith
    have hp : (2 : ℝ) ^ F.fractionBits < (2 : ℝ) ^ F.precision := by
      unfold precision
      rw [pow_succ]
      have : 0 < (2 : ℝ) ^ F.fractionBits := by positivity
      linarith
    have hepow : (2 : ℝ) ^ F.precision * (2 : ℝ) ^ e =
        (2 : ℝ) ^ F.fractionBits * (2 : ℝ) ^ (e + 1) := by
      simp [precision, pow_succ, zpow_add₀]
      ring
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ F.precision)).mp heq with hmpos | hmneg
    · refine ⟨(2 : ℤ) ^ F.fractionBits, e + 1, by omega, by omega, ?_, ?_⟩
      · simpa using hp
      · change (m : ℝ) * (2 : ℝ) ^ e = _
        rw [hmpos]
        simpa using hepow
    · refine ⟨-((2 : ℤ) ^ F.fractionBits), e + 1, by omega, by omega, ?_, ?_⟩
      · simpa using hp
      · change (m : ℝ) * (2 : ℝ) ^ e = _
        rw [hmneg]
        push_cast
        nlinarith [hepow]

/-- The formula rounds to a nearest member of the *whole* finite value set,
not merely to a point in the selected binade's lattice. -/
theorem roundFinite_nearest (F : Format) (x z : ℝ) (hz : F.Representable z) :
    |F.roundFinite x - x| ≤ |z - x| := by
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨m, e, hel, _, hm, rfl⟩ := hz
  by_cases he : F.quantumExponent x ≤ e
  · let k : ℤ := m * (2 : ℤ) ^ (e - F.quantumExponent x).toNat
    have heq : (k : ℝ) * F.quantum x = (m : ℝ) * (2 : ℝ) ^ e := by
      have hpow : (2 : ℝ) ^ (e - F.quantumExponent x).toNat * F.quantum x =
          (2 : ℝ) ^ e := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), quantum,
          ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        omega
      dsimp [k]
      push_cast
      rw [mul_assoc, hpow]
    simpa only [heq, roundFinite] using scaled_roundEven_nearest x _ (F.quantum_pos x) k
  · let B : ℝ := (2 : ℝ) ^ F.fractionBits * F.quantum x
    have hmax : max F.emin (Int.log 2 |x|) = Int.log 2 |x| := by
      unfold quantumExponent at he
      omega
    have hB : B = (2 : ℝ) ^ Int.log 2 |x| := by
      dsimp [B]
      rw [← zpow_natCast, quantum, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      unfold quantumExponent
      rw [hmax]
      omega
    have hBx : B ≤ |x| := by
      rw [hB]
      exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
    have hsmall : |(m : ℝ) * (2 : ℝ) ^ e| ≤ B := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ e)]
      calc
        |(m : ℝ)| * (2 : ℝ) ^ e ≤ (2 : ℝ) ^ F.precision * (2 : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right hm.le (by positivity)
        _ ≤ (2 : ℝ) ^ F.precision * (2 : ℝ) ^ (F.quantumExponent x - 1) :=
          mul_le_mul_of_nonneg_left
            (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by positivity)
        _ = B := by
          rw [pow_precision, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          dsimp [B]
          rw [← zpow_natCast, quantum, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1
          omega
    have hdist : |x| ≤ |(m : ℝ) * (2 : ℝ) ^ e - x| + B := by
      have ht := abs_add_le (x - (m : ℝ) * (2 : ℝ) ^ e) ((m : ℝ) * (2 : ℝ) ^ e)
      rw [sub_add_cancel, abs_sub_comm x] at ht
      linarith
    by_cases hs : 0 ≤ x
    · have hn := scaled_roundEven_nearest x _ (F.quantum_pos x) ((2 : ℤ) ^ F.fractionBits)
      have heq : (((2 : ℤ) ^ F.fractionBits : ℤ) : ℝ) * F.quantum x = B := by
        simp [B]
      rw [heq] at hn
      rw [abs_of_nonneg hs] at hBx hdist
      rw [abs_of_nonpos (by linarith : B - x ≤ 0)] at hn
      change |F.roundFinite x - x| ≤ _ at hn
      linarith
    · have hn := scaled_roundEven_nearest x _ (F.quantum_pos x) (-((2 : ℤ) ^ F.fractionBits))
      have heq : ((-((2 : ℤ) ^ F.fractionBits) : ℤ) : ℝ) * F.quantum x = -B := by
        simp [B]
      rw [heq] at hn
      rw [abs_of_neg (by linarith : x < 0)] at hBx hdist
      rw [abs_of_nonneg (by linarith : 0 ≤ -B - x)] at hn
      change |F.roundFinite x - x| ≤ _ at hn
      linarith

/-- Representable values round exactly, including every subnormal. -/
theorem roundFinite_exact (F : Format) {x : ℝ} (hx : F.Representable x) :
    F.roundFinite x = x := by
  have he := F.roundFinite_nearest x x hx
  simpa only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] using he

/-- A local mixed absolute/relative error bound valid even under gradual
underflow. The pure relative theorem uses the normal-range specialization. -/
theorem roundFinite_mixed_error (F : Format) (x : ℝ) :
    |F.roundFinite x - x| ≤ F.unitRoundoff * |x| + F.minSubnormal / 2 := by
  by_cases hx : x = 0
  · subst x
    simp only [roundFinite_zero, sub_self, abs_zero, mul_zero, zero_add]
    unfold minSubnormal
    positivity
  by_cases he : F.emin ≤ Int.log 2 |x|
  · have hn : F.minNormal ≤ |x| := by
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) (abs_pos.mpr hx)).mpr he
    have herr := (F.roundFinite_abs_error x).trans (F.half_quantum_le_relative hn)
    have heta : 0 ≤ F.minSubnormal / 2 := by unfold minSubnormal; positivity
    linarith
  · have hq : F.quantum x = F.minSubnormal := by
      simp only [quantum, quantumExponent, max_eq_left (by omega : Int.log 2 |x| ≤ F.emin),
        minSubnormal]
    have herr := F.roundFinite_abs_error x
    rw [hq] at herr
    have hu := mul_nonneg F.unitRoundoff_pos.le (abs_nonneg x)
    linarith

end FP.IEEE.Format
