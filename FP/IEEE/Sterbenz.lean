import FP.IEEE.Representation

/-! Exact cancellation in a finite binary format, including gradual underflow. -/
noncomputable section
namespace FP.IEEE.Format

/-- A binary number lies on every finer binary lattice. -/
theorem integer_mul_zpow_refine (m e d : ℤ) (hde : d ≤ e) :
    ∃ k : ℤ, (m : ℝ) * (2 : ℝ)^e = (k : ℝ) * (2 : ℝ)^d := by
  refine ⟨m * (2 : ℤ)^(e-d).toNat, ?_⟩
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

/-- A lattice point no larger than a representable value on that lattice is
representable. This supplies the mantissa bound without normalizing the point. -/
theorem representable_of_lattice_le (F : Format) (m k e : ℤ)
    (hel : F.emin - F.fractionBits ≤ e) (heu : e ≤ F.emax - F.fractionBits)
    (hm : |(m : ℝ)| < (2 : ℝ)^F.precision)
    (hk : |(k : ℝ) * (2 : ℝ)^e| ≤ |(m : ℝ) * (2 : ℝ)^e|) :
    F.Representable ((k : ℝ) * (2 : ℝ)^e) := by
  refine ⟨k, e, hel, heu, ?_, rfl⟩
  rw [abs_mul, abs_mul] at hk
  exact (le_of_mul_le_mul_right hk (abs_pos.mpr (zpow_ne_zero _ (by norm_num)))).trans_lt hm

/-- Cancellation is exact when the difference is no larger than either operand.
The proof uses the finer of their two representation lattices. -/
theorem representable_sub_of_abs_le (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hsmallx : |x-y| ≤ |x|) (hsmally : |x-y| ≤ |y|) :
    F.Representable (x-y) := by
  obtain ⟨m, e, hel, heu, hm, rfl⟩ := hx
  obtain ⟨n, d, hdl, hdu, hn, rfl⟩ := hy
  rcases le_total e d with hed | hde
  · obtain ⟨k, hk⟩ := integer_mul_zpow_refine n d e hed
    have heq : (m : ℝ) * 2^e - (n : ℝ) * 2^d = ((m-k : ℤ) : ℝ) * 2^e := by
      rw [hk]
      push_cast
      ring
    rw [heq] at hsmallx ⊢
    exact F.representable_of_lattice_le m (m-k) e hel heu hm hsmallx
  · obtain ⟨k, hk⟩ := integer_mul_zpow_refine m e d hde
    have heq : (m : ℝ) * 2^e - (n : ℝ) * 2^d = ((k-n : ℤ) : ℝ) * 2^d := by
      rw [hk]
      push_cast
      ring
    rw [heq] at hsmally ⊢
    exact F.representable_of_lattice_le n (k-n) d hdl hdu hn hsmally

/-- Sterbenz's lemma, including zeros and subnormals: two nonnegative finite
binary values within a factor of two have a representable exact difference. -/
theorem sterbenz (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2*x) :
    F.Representable (x-y) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  apply F.representable_sub_of_abs_le hx hy
  · rw [abs_of_nonneg hx0, abs_le]
    constructor <;> linarith
  · rw [abs_of_nonneg hy0, abs_le]
    constructor <;> linarith

/-- Negation preserves finite representability. -/
theorem representable_neg (F : Format) {x : ℝ} (hx : F.Representable x) :
    F.Representable (-x) := by
  obtain ⟨m, e, hl, hu, hm, rfl⟩ := hx
  exact ⟨-m, e, hl, hu, by simpa using hm, by simp⟩

/-- The magnitude formulation also covers two negative operands. -/
theorem sterbenz_abs (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hsign : 0 ≤ x*y) (hxy : |x| / 2 ≤ |y|) (hyx : |y| ≤ 2*|x|) :
    F.Representable (x-y) := by
  by_cases hx0 : 0 ≤ x
  · by_cases hy0 : 0 ≤ y
    · exact F.sterbenz hx hy (by simpa [abs_of_nonneg hx0, abs_of_nonneg hy0] using hxy)
        (by simpa [abs_of_nonneg hx0, abs_of_nonneg hy0] using hyx)
    · have hxz : x = 0 := by nlinarith
      have hyz : y = 0 := by exact abs_nonpos_iff.mp (by simpa [hxz] using hyx)
      simp [hxz, hyz, F.representable_zero]
  · have hy0 : y ≤ 0 := by nlinarith
    have h := F.sterbenz (F.representable_neg hx) (F.representable_neg hy)
      (by simpa [abs_of_nonpos (le_of_not_ge hx0), abs_of_nonpos hy0] using hxy)
      (by simpa [abs_of_nonpos (le_of_not_ge hx0), abs_of_nonpos hy0] using hyx)
    simpa [sub_eq_add_neg, add_comm] using F.representable_neg h

/-- Nearest-even subtraction in the real model incurs no error under Sterbenz. -/
theorem roundFinite_sub_sterbenz (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2*x) :
    F.roundFinite (x-y) = x-y :=
  F.roundFinite_exact (F.sterbenz hx hy hxy hyx)

end FP.IEEE.Format
