import FP.IEEE.Sterbenz

/-! Representability of the exact rounding error of binary addition. -/
noncomputable section
namespace FP.IEEE.Format

/-- A rounded lattice input either stays exact or retains its original lattice.
If its error fits an available mantissa on that lattice, that error is finite. -/
theorem roundFinite_residual_of_lattice (F : Format) (m k e : ℤ)
    (hel : F.emin - F.fractionBits ≤ e) (heu : e ≤ F.emax - F.fractionBits)
    (hm : |(m : ℝ)| < (2 : ℝ)^F.precision)
    (hb : |(k : ℝ)*2^e - F.roundFinite ((k : ℝ)*2^e)| ≤ |(m : ℝ)*2^e|) :
    F.Representable ((k : ℝ)*2^e - F.roundFinite ((k : ℝ)*2^e)) := by
  let t : ℝ := (k : ℝ)*2^e
  by_cases he : F.quantumExponent t ≤ e
  · obtain ⟨j, hj⟩ := integer_mul_zpow_refine k e (F.quantumExponent t) he
    have ht : t / F.quantum t = (j : ℝ) := by
      apply (div_eq_iff (ne_of_gt (F.quantum_pos t))).mpr
      exact hj
    have hr : F.roundFinite t = t := by
      rw [roundFinite, ht, roundEven_intCast]
      exact hj.symm
    change F.Representable (t-F.roundFinite t)
    rw [hr, sub_self]
    exact F.representable_zero
  · obtain ⟨j, hj⟩ := integer_mul_zpow_refine
      (roundEven (t/F.quantum t)) (F.quantumExponent t) e (by omega)
    have ht : t-F.roundFinite t = ((k-j : ℤ) : ℝ)*2^e := by
      change t - (roundEven (t/F.quantum t) : ℝ)*2^(F.quantumExponent t) = _
      rw [hj]
      dsimp [t]
      push_cast
      ring
    change F.Representable (t-F.roundFinite t)
    change |t-F.roundFinite t| ≤ _ at hb
    rw [ht] at hb ⊢
    exact F.representable_of_lattice_le m (k-j) e hel heu hm hb

/-- The exact rounding error of an addition is itself representable, including
when the error is subnormal. This theorem does not assume exact reconstruction
operations or a successful runtime certificate. -/
theorem roundFinite_add_residual_representable (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) :
    F.Representable (x+y-F.roundFinite (x+y)) := by
  have hbx : |x+y-F.roundFinite (x+y)| ≤ |x| := by
    simpa [abs_sub_comm] using F.roundFinite_nearest (x+y) y hy
  have hby : |x+y-F.roundFinite (x+y)| ≤ |y| := by
    simpa [abs_sub_comm] using F.roundFinite_nearest (x+y) x hx
  obtain ⟨m, e, hel, heu, hm, rfl⟩ := hx
  obtain ⟨n, d, hdl, hdu, hn, rfl⟩ := hy
  rcases le_total e d with hed | hde
  · obtain ⟨j, hj⟩ := integer_mul_zpow_refine n d e hed
    have ht : (m : ℝ)*2^e + (n : ℝ)*2^d = ((m+j : ℤ) : ℝ)*2^e := by
      rw [hj]
      push_cast
      ring
    rw [ht] at hbx ⊢
    exact F.roundFinite_residual_of_lattice m (m+j) e hel heu hm hbx
  · obtain ⟨j, hj⟩ := integer_mul_zpow_refine m e d hde
    have ht : (m : ℝ)*2^e + (n : ℝ)*2^d = ((j+n : ℤ) : ℝ)*2^d := by
      rw [hj]
      push_cast
      ring
    rw [ht] at hby ⊢
    exact F.roundFinite_residual_of_lattice n (j+n) d hdl hdu hn hby

/-- The same exact-residual property holds for subtraction. -/
theorem roundFinite_sub_residual_representable (F : Format) {x y : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) :
    F.Representable (x-y-F.roundFinite (x-y)) := by
  simpa [sub_eq_add_neg] using F.roundFinite_add_residual_representable hx (F.representable_neg hy)

end FP.IEEE.Format
