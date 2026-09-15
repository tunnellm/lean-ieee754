import FP.IEEE.RoundingBounds

/-! Exact product residuals above the lower lattice boundary, and a sharp
absolute defect bound when the FMA residual itself must round. -/
noncomputable section
namespace FP.IEEE.Format

private theorem wide_quantum_bound (F : Format) (k e : ℤ)
    (hk : |(k : ℝ)| < (2 : ℝ)^(2*F.precision)) (hz : (k : ℝ)*2^e ≠ 0) :
    F.quantumExponent ((k : ℝ)*2^e) ≤ max (F.emin-F.fractionBits) (e+F.precision) := by
  have ht : |(k : ℝ)*2^e| < (2 : ℝ)^((2*F.precision : ℕ)+e) := by
    rw [abs_mul,abs_of_pos (by positivity : (0 : ℝ)<2^e)]
    have hh := mul_lt_mul_of_pos_right hk (by positivity : (0 : ℝ)<2^e)
    simpa only [← zpow_natCast,← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hl := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) (abs_pos.mpr hz)).mp ht
  unfold quantumExponent precision at *
  omega

private theorem exact_of_quantum_le (F : Format) (k e : ℤ)
    (he : F.quantumExponent ((k : ℝ)*2^e) ≤ e) :
    F.roundFinite ((k : ℝ)*2^e) = (k : ℝ)*2^e := by
  obtain ⟨j,hj⟩ := integer_mul_zpow_refine k e _ he
  have ht : (k : ℝ)*2^e/F.quantum ((k : ℝ)*2^e) = (j : ℝ) :=
    (div_eq_iff (ne_of_gt (F.quantum_pos _))).mpr hj
  rw [roundFinite,ht,roundEven_intCast]
  exact hj.symm

/-- A product-sized significand has an exactly representable residual whenever
its lattice lies above the least-subnormal lattice and its high result is finite. -/
theorem roundFinite_residual_representable_of_wide_lattice (F : Format) (k e : ℤ)
    (hk : |(k : ℝ)| < (2 : ℝ)^(2*F.precision))
    (he : F.emin-F.fractionBits ≤ e)
    (hr : |(k : ℝ)*2^e| < F.overflowThreshold) :
    F.Representable ((k : ℝ)*2^e-F.roundFinite ((k : ℝ)*2^e)) := by
  by_cases hz : (k : ℝ)*2^e = 0
  · simp [hz,F.representable_zero]
  by_cases hq : F.quantumExponent ((k : ℝ)*2^e) ≤ e
  · rw [exact_of_quantum_le F k e hq,sub_self]
    exact F.representable_zero
  have hu : e ≤ F.emax-F.fractionBits := by
    have := F.quantumExponent_le_of_noOverflow hr hz
    omega
  have hqb : F.quantumExponent ((k : ℝ)*2^e) ≤ e+F.precision := by
    have := wide_quantum_bound F k e hk hz
    have : 0 ≤ (F.precision : ℤ) := by omega
    omega
  have hpow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hqb
  have heq : (2 : ℝ)^(e+(F.precision : ℤ))/2 = (2 : ℝ)^F.fractionBits*2^e := by
    simp [precision,zpow_add₀,zpow_natCast,pow_succ]
    ring
  apply F.roundFinite_residual_of_lattice ((2 : ℤ)^F.fractionBits) k e he hu
  · simp [precision,pow_succ,abs_of_pos (pow_pos (by norm_num : (0 : ℝ)<2) _)]
  · have hb := F.roundFinite_abs_error ((k : ℝ)*2^e)
    rw [abs_sub_comm] at hb
    have hh := hb.trans (div_le_div_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ 2))
    simpa [heq,abs_mul,abs_of_pos (by positivity : (0 : ℝ)<2^e)] using hh

private theorem wide_residual_small (F : Format) (k e : ℤ)
    (hk : |(k : ℝ)| < (2 : ℝ)^(2*F.precision)) (he : e < F.emin-F.fractionBits) :
    |(k : ℝ)*2^e-F.roundFinite ((k : ℝ)*2^e)| ≤ F.minNormal/2 := by
  by_cases hz : (k : ℝ)*2^e = 0
  · simp only [hz,roundFinite_zero,sub_self,abs_zero]
    unfold minNormal; positivity
  have hq : F.quantumExponent ((k : ℝ)*2^e) ≤ F.emin := by
    have := wide_quantum_bound F k e hk hz
    unfold precision at *
    omega
  have hp := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq
  have hb : |(k : ℝ)*2^e-F.roundFinite ((k : ℝ)*2^e)| ≤ F.quantum ((k : ℝ)*2^e)/2 := by
    simpa [abs_sub_comm] using F.roundFinite_abs_error ((k : ℝ)*2^e)
  exact hb.trans (div_le_div_of_nonneg_right hp (by norm_num))

/-- Rounding an input smaller than the normal boundary loses at most half a
least subnormal, including zero. -/
theorem roundFinite_small_error (F : Format) (t : ℝ) (ht : |t| ≤ F.minNormal) :
    |F.roundFinite t-t| ≤ F.minSubnormal/2 := by
  by_cases hz : t = 0
  · subst t; simp only [roundFinite_zero,sub_self,abs_zero]; unfold minSubnormal; positivity
  have hpow : F.minNormal < (2 : ℝ)^(F.emin+1) := by
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hlog := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) (abs_pos.mpr hz)).mp (ht.trans_lt hpow)
  have hl : Int.log 2 |t| ≤ F.emin := by omega
  have hq : F.quantumExponent t = F.emin-F.fractionBits := by unfold quantumExponent; omega
  simpa only [quantum,hq,minSubnormal] using F.roundFinite_abs_error t

/-- FMA recovery of a finite product loses at most half a least subnormal. -/
theorem roundFinite_product_residual_error (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hr : |x*y| < F.overflowThreshold) :
    |F.roundFinite (x*y-F.roundFinite (x*y))-(x*y-F.roundFinite (x*y))| ≤ F.minSubnormal/2 := by
  obtain ⟨m,e,_,_,hm,rfl⟩ := hx
  obtain ⟨n,d,_,_,hn,rfl⟩ := hy
  have heq : (m : ℝ)*2^e*((n : ℝ)*2^d) = ((m*n : ℤ) : ℝ)*2^(e+d) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast; ring
  rw [heq] at hr ⊢
  have hmn : |((m*n : ℤ) : ℝ)| < (2 : ℝ)^(2*F.precision) := by
    rw [Int.cast_mul,abs_mul,show 2*F.precision = F.precision+F.precision by omega,pow_add]
    exact (mul_le_mul_of_nonneg_right hm.le (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hn (by positivity))
  by_cases he : F.emin-F.fractionBits ≤ e+d
  · rw [F.roundFinite_exact (F.roundFinite_residual_representable_of_wide_lattice _ _ hmn he hr),sub_self,abs_zero]
    unfold minSubnormal; positivity
  · apply F.roundFinite_small_error
    have hs := wide_residual_small F (m*n) (e+d) hmn (by omega)
    have hp : 0 ≤ F.minNormal := by unfold minNormal; positivity
    linarith

end FP.IEEE.Format
