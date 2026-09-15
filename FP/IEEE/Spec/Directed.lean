import FP.IEEE.Spec.RealRounding

/-! Directed rounding is extremal over the whole finite value set. -/
namespace FP.IEEE.Spec
noncomputable section

theorem roundWithMode_up (F : Format) (x : ℝ) : x ≤ roundWithMode F .towardPositive x := by
  exact (div_le_iff₀ (F.quantum_pos x)).mp (Int.le_ceil (x / F.quantum x))

theorem roundWithMode_down (F : Format) (x : ℝ) : roundWithMode F .towardNegative x ≤ x := by
  exact (le_div_iff₀ (F.quantum_pos x)).mp (Int.floor_le (x / F.quantum x))

private theorem up_lattice (F : Format) (x : ℝ) (k : ℤ) (h : x ≤ (k : ℝ)*F.quantum x) :
    roundWithMode F .towardPositive x ≤ (k : ℝ)*F.quantum x := by
  have hi := Int.ceil_le.mpr ((div_le_iff₀ (F.quantum_pos x)).mpr h)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (F.quantum_pos x).le

private theorem down_lattice (F : Format) (x : ℝ) (k : ℤ) (h : (k : ℝ)*F.quantum x ≤ x) :
    (k : ℝ)*F.quantum x ≤ roundWithMode F .towardNegative x := by
  have hi := Int.le_floor.mpr ((le_div_iff₀ (F.quantum_pos x)).mpr h)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (F.quantum_pos x).le

private theorem coarse (F : Format) (x : ℝ) (hx : x ≠ 0) (m e : ℤ)
    (hel : F.emin - F.fractionBits ≤ e) (hm : |(m : ℝ)| < (2 : ℝ)^F.precision)
    (he : e < F.quantumExponent x) :
    let B := (2 : ℝ)^F.fractionBits * F.quantum x
    B ≤ |x| ∧ |(m : ℝ)*(2 : ℝ)^e| ≤ B := by
  dsimp only
  have hmax : max F.emin (Int.log 2 |x|) = Int.log 2 |x| := by
    unfold Format.quantumExponent at he; omega
  have hB : (2 : ℝ)^F.fractionBits * F.quantum x = (2 : ℝ)^Int.log 2 |x| := by
    rw [← zpow_natCast, Format.quantum, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    unfold Format.quantumExponent
    rw [hmax]; omega
  refine ⟨by rw [hB]; exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx), ?_⟩
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^e)]
  calc
    _ ≤ (2 : ℝ)^F.precision * (2 : ℝ)^e := mul_le_mul_of_nonneg_right hm.le (by positivity)
    _ ≤ (2 : ℝ)^F.precision * (2 : ℝ)^(F.quantumExponent x - 1) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = _ := by
      rw [Format.precision, pow_succ, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp [Format.quantum]
      ring

private theorem lattice (F : Format) (x : ℝ) (m e : ℤ) (he : F.quantumExponent x ≤ e) :
    ∃ k : ℤ, (k : ℝ)*F.quantum x = (m : ℝ)*(2 : ℝ)^e := by
  refine ⟨m * (2 : ℤ)^(e - F.quantumExponent x).toNat, ?_⟩
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega), Format.quantum,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

/-- No finite representable upper bound lies below the upward-rounded result. -/
theorem roundWithMode_up_le (F : Format) (x z : ℝ) (hz : F.Representable z) (hxz : x ≤ z) :
    roundWithMode F .towardPositive x ≤ z := by
  by_cases hx : x = 0
  · subst x; simpa [roundWithMode] using hxz
  obtain ⟨m, e, hel, _, hm, rfl⟩ := hz
  by_cases he : F.quantumExponent x ≤ e
  · obtain ⟨k, hk⟩ := lattice F x m e he
    rw [← hk] at hxz ⊢
    exact up_lattice F x k hxz
  obtain ⟨hBx, hsmall⟩ := coarse F x hx m e hel hm (lt_of_not_ge he)
  have hp : (((2 : ℤ)^F.fractionBits : ℤ) : ℝ)*F.quantum x = (2 : ℝ)^F.fractionBits*F.quantum x := by simp
  have hn : ((-((2 : ℤ)^F.fractionBits) : ℤ) : ℝ)*F.quantum x = -((2 : ℝ)^F.fractionBits*F.quantum x) := by simp
  by_cases hs : 0 ≤ x
  · rw [abs_of_nonneg hs] at hBx
    have hzB := (le_abs_self ((m : ℝ)*2^e)).trans hsmall
    have h := up_lattice F x ((2 : ℤ)^F.fractionBits) (by rw [hp]; exact hxz.trans hzB)
    rw [hp] at h
    exact h.trans (hBx.trans hxz)
  · rw [abs_of_neg (lt_of_not_ge hs)] at hBx
    have h := up_lattice F x (-((2 : ℤ)^F.fractionBits)) (by rw [hn]; linarith)
    rw [hn] at h
    exact h.trans (by linarith [(abs_le.mp hsmall).1])

/-- No finite representable lower bound lies above the downward-rounded result. -/
theorem roundWithMode_le_down (F : Format) (x z : ℝ) (hz : F.Representable z) (hxz : z ≤ x) :
    z ≤ roundWithMode F .towardNegative x := by
  by_cases hx : x = 0
  · subst x; simpa [roundWithMode] using hxz
  obtain ⟨m, e, hel, _, hm, rfl⟩ := hz
  by_cases he : F.quantumExponent x ≤ e
  · obtain ⟨k, hk⟩ := lattice F x m e he
    rw [← hk] at hxz ⊢
    exact down_lattice F x k hxz
  obtain ⟨hBx, hsmall⟩ := coarse F x hx m e hel hm (lt_of_not_ge he)
  have hp : (((2 : ℤ)^F.fractionBits : ℤ) : ℝ)*F.quantum x = (2 : ℝ)^F.fractionBits*F.quantum x := by simp
  have hn : ((-((2 : ℤ)^F.fractionBits) : ℤ) : ℝ)*F.quantum x = -((2 : ℝ)^F.fractionBits*F.quantum x) := by simp
  by_cases hs : 0 ≤ x
  · rw [abs_of_nonneg hs] at hBx
    have h := down_lattice F x ((2 : ℤ)^F.fractionBits) (by rw [hp]; exact hBx)
    rw [hp] at h
    exact ((le_abs_self _).trans hsmall).trans h
  · rw [abs_of_neg (lt_of_not_ge hs)] at hBx
    have hBz := (abs_le.mp hsmall).1
    have h := down_lattice F x (-((2 : ℤ)^F.fractionBits)) (by rw [hn]; exact hBz.trans hxz)
    rw [hn] at h
    exact (show (m : ℝ)*2^e ≤ -((2 : ℝ)^F.fractionBits*F.quantum x) by linarith).trans h
end
end FP.IEEE.Spec
