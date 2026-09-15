import FP.IEEE.Roundoff

/-! Order bounds and lattice preservation for nearest-even binary rounding. -/
noncomputable section
namespace FP.IEEE

theorem roundEven_neg (x : ℝ) : roundEven (-x) = -roundEven x := by
  by_cases hx : x = (⌊x⌋ : ℝ)
  · conv_lhs => rw [hx]
    rw [← Int.cast_neg, roundEven_intCast]
    conv_rhs => rw [hx]
    simp
  · have hlo := Int.floor_le x
    have hhi := Int.lt_floor_add_one x
    have hstrict : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne hlo (Ne.symm hx)
    have hf : ⌊-x⌋ = -⌊x⌋-1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hm0 := Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
    have hm1 := Int.emod_lt_of_pos ⌊x⌋ (by norm_num : (0 : ℤ) < 2)
    have hm : (-⌊x⌋-1)%2 = 1-⌊x⌋%2 := by omega
    unfold roundEven
    rw [hf]
    push_cast
    split_ifs <;> first | omega | linarith

namespace Format

@[simp] theorem roundFinite_neg (F : Format) (x : ℝ) :
    F.roundFinite (-x) = -F.roundFinite x := by
  have hq : F.quantum (-x) = F.quantum x := by simp [quantum, quantumExponent]
  simp [roundFinite, hq, neg_div, roundEven_neg]


/-- Nearest rounding cannot cross a representable lower endpoint. -/
theorem le_roundFinite (F : Format) {t z : ℝ} (hz : F.Representable z) (ht : z ≤ t) :
    z ≤ F.roundFinite t := by
  have h := F.roundFinite_nearest t z hz
  by_contra hn
  rw [abs_of_nonpos (by linarith : F.roundFinite t-t ≤ 0),
    abs_of_nonpos (by linarith : z-t ≤ 0)] at h
  linarith

/-- Nearest rounding cannot cross a representable upper endpoint. -/
theorem roundFinite_le (F : Format) {t z : ℝ} (hz : F.Representable z) (ht : t ≤ z) :
    F.roundFinite t ≤ z := by
  have h := F.roundFinite_nearest t z hz
  by_contra hn
  rw [abs_of_nonneg (by linarith : 0 ≤ F.roundFinite t-t),
    abs_of_nonneg (by linarith : 0 ≤ z-t)] at h
  linarith

theorem roundFinite_nonneg (F : Format) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ F.roundFinite t := F.le_roundFinite F.representable_zero ht

/-- Rounding retains every binary lattice already containing the input. -/
theorem roundFinite_lattice (F : Format) (k e : ℤ) :
    ∃ j : ℤ, F.roundFinite ((k : ℝ)*2^e) = (j : ℝ)*2^e := by
  let t : ℝ := (k : ℝ)*2^e
  by_cases he : F.quantumExponent t ≤ e
  · obtain ⟨j, hj⟩ := integer_mul_zpow_refine k e (F.quantumExponent t) he
    have ht : t / F.quantum t = (j : ℝ) := (div_eq_iff (ne_of_gt (F.quantum_pos t))).mpr hj
    refine ⟨k, ?_⟩
    change F.roundFinite t = t
    rw [roundFinite, ht, roundEven_intCast]
    exact hj.symm
  · exact integer_mul_zpow_refine (roundEven (t/F.quantum t))
      (F.quantumExponent t) e (by omega)

theorem representable_min_lattice (F : Format) {x : ℝ} (hx : F.Representable x) :
    ∃ k : ℤ, x = (k : ℝ)*F.minSubnormal := by
  obtain ⟨m,e,hl,_,_,rfl⟩ := hx
  exact integer_mul_zpow_refine m e _ hl

theorem add_min_lattice (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) :
    ∃ k : ℤ, x+y = (k : ℝ)*F.minSubnormal := by
  obtain ⟨m,rfl⟩ := F.representable_min_lattice hx
  obtain ⟨n,rfl⟩ := F.representable_min_lattice hy
  exact ⟨m+n, by push_cast; ring⟩

theorem sub_min_lattice (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) :
    ∃ k : ℤ, x-y = (k : ℝ)*F.minSubnormal := by
  simpa [sub_eq_add_neg] using F.add_min_lattice hx (F.representable_neg hy)

theorem minNormal_representable (F : Format) : F.Representable F.minNormal := by
  refine ⟨(2 : ℤ)^F.fractionBits, F.emin-F.fractionBits, le_rfl,
    sub_le_sub_right F.exponent_order _, ?_, ?_⟩
  · simp only [Int.cast_pow, Int.cast_ofNat, abs_of_pos (by positivity : (0 : ℝ)<2^F.fractionBits)]
    rw [precision, pow_succ]
    linarith [pow_pos (by norm_num : (0 : ℝ)<2) F.fractionBits]
  · simp only [Int.cast_pow, Int.cast_ofNat, minNormal]
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega

theorem precision_mul_minSubnormal (F : Format) :
    (2 : ℝ)^F.precision * F.minSubnormal = 2*F.minNormal := by
  rw [precision, minSubnormal, minNormal, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  have he : (F.fractionBits : ℤ)+1+(F.emin-F.fractionBits) = F.emin+1 := by ring
  rw [he, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp [mul_comm]

/-- Every sufficiently small point of the subnormal lattice is exact. -/
theorem roundFinite_small_lattice (F : Format) (k : ℤ)
    (hk : |(k : ℝ)*F.minSubnormal| < 2*F.minNormal) :
    F.roundFinite ((k : ℝ)*F.minSubnormal) = (k : ℝ)*F.minSubnormal := by
  apply F.roundFinite_exact
  refine ⟨k, F.emin-F.fractionBits, le_rfl, sub_le_sub_right F.exponent_order _, ?_, rfl⟩
  rw [← F.precision_mul_minSubnormal, abs_mul,
    abs_of_pos (by unfold minSubnormal; positivity : 0 < F.minSubnormal)] at hk
  exact (mul_lt_mul_iff_left₀ (by unfold minSubnormal; positivity : 0 < F.minSubnormal)).mp hk

/-- Halving a value above the first normal binade is representable. -/
theorem representable_half (F : Format) {x : ℝ} (hx : F.Representable x)
    (hb : 2*F.minNormal ≤ |x|) : F.Representable (x/2) := by
  obtain ⟨m,e,hl,hu,hm,rfl⟩ := hx
  have he : F.emin-F.fractionBits < e := by
    by_contra hn
    have he : e = F.emin-F.fractionBits := by omega
    rw [he, ← F.precision_mul_minSubnormal] at hb
    change (2 : ℝ)^F.precision*F.minSubnormal ≤ |(m : ℝ)*F.minSubnormal| at hb
    rw [abs_mul, abs_of_pos (by unfold minSubnormal; positivity : 0 < F.minSubnormal)] at hb
    have h := (mul_le_mul_iff_left₀ (by unfold minSubnormal; positivity : 0<F.minSubnormal)).mp hb
    linarith
  refine ⟨m,e-1,by omega,by omega,hm,?_⟩
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_one]
  ring

/-- An input on the IEEE lattice cannot round below half a representable bound.
The lattice premise handles halves smaller than the normal range. -/
theorem half_le_roundFinite (F : Format) {x t : ℝ} (hx : F.Representable x)
    (hx0 : 0 ≤ x) (ht : x/2 ≤ t)
    (hl : ∃ k : ℤ, t = (k : ℝ)*F.minSubnormal) :
    x/2 ≤ F.roundFinite t := by
  by_cases hb : 2*F.minNormal ≤ x
  · exact F.le_roundFinite (F.representable_half hx (by simpa [abs_of_nonneg hx0] using hb)) ht
  · by_cases hn : F.minNormal ≤ t
    · exact (by linarith : x/2 ≤ F.minNormal).trans (F.le_roundFinite F.minNormal_representable hn)
    · obtain ⟨k,rfl⟩ := hl
      have ht0 : 0 ≤ (k : ℝ)*F.minSubnormal := by linarith
      rw [F.roundFinite_small_lattice k (by
        rw [abs_of_nonneg ht0]
        have : 0 < F.minNormal := by unfold minNormal; positivity
        linarith)]
      exact ht

private def wider (F : Format) : Format :=
  { F with emax := F.emax+1, exponent_order := by have := F.exponent_order; omega }

private theorem wider_double (F : Format) {x : ℝ} (hx : F.Representable x) :
    (wider F).Representable (2*x) := by
  obtain ⟨m,e,hl,hu,hm,rfl⟩ := hx
  refine ⟨m,e+1,by dsimp [wider]; omega,by dsimp [wider]; omega,hm,?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_one]
  ring

/-- Doubling is an exact precision value, even beyond the finite upper limit. -/
theorem double_le_roundFinite (F : Format) {x t : ℝ} (hx : F.Representable x)
    (ht : 2*x ≤ t) : 2*x ≤ F.roundFinite t :=
  (wider F).le_roundFinite (wider_double F hx) ht

theorem roundFinite_le_double (F : Format) {x t : ℝ} (hx : F.Representable x)
    (ht : t ≤ 2*x) : F.roundFinite t ≤ 2*x :=
  (wider F).roundFinite_le (wider_double F hx) ht

end Format
end FP.IEEE
