import FP.Native.Unpack

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

theorem representable_lt_top (F : FP.IEEE.Format) {x : ℝ} (hx : F.Representable x) :
    |x| < (2 : ℝ) ^ (F.emax + 1) := by
  obtain ⟨m, e, _, he, hm, rfl⟩ := hx
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ e)]
  calc
    |(m : ℝ)| * (2 : ℝ) ^ e < (2 : ℝ) ^ F.precision * (2 : ℝ) ^ e :=
      mul_lt_mul_of_pos_right hm (by positivity)
    _ ≤ (2 : ℝ) ^ F.precision * (2 : ℝ) ^ (F.emax - F.fractionBits) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) he) (by positivity)
    _ = (2 : ℝ) ^ (F.emax + 1) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      simp [FP.IEEE.Format.precision]
      omega

theorem canonical_exponent_le {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (hmax : F.emax = (S.exponentBias : ℤ))
    (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (hc : Canonical S (.finite s m e hm))
    (hr : F.Representable ((s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e)) :
    e ≤ (S.exponentBias : ℤ) - S.mantissaBitsWithoutImplicit := by
  rcases hc.2.2 with hn | he
  · have hx := representable_lt_top F hr
    have habs : |(s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e| = (m : ℝ) * (2 : ℝ) ^ e := by
      cases s <;> simp [Sign.apply, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ e)]
    rw [habs] at hx
    have hlo : (2 : ℝ) ^ ((S.mantissaBitsWithoutImplicit : ℤ) + e) ≤ (m : ℝ) * (2 : ℝ) ^ e := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    have hh : (S.mantissaBitsWithoutImplicit : ℤ) + e < F.emax + 1 :=
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hlo.trans_lt hx)
    rw [hmax] at hh
    omega
  · rw [he, hSF.minExponent, hSF.fractionBits, ← hmax]
    exact sub_le_sub_right F.exponent_order _

/-- Packing preserves the real value of a canonical result that fits the
specification. No assumption about the native packer's behavior is needed. -/
theorem pack_value {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (hmax : F.emax = (S.exponentBias : ℤ))
    (a : UnpackedFloat) (x : ℝ) (hc : Canonical S a)
    (hv : unpackedValue a = some x) (hr : F.Representable x) :
    wordValue S (pack S a) = some x := by
  cases a with
  | infinity s => simp [unpackedValue] at hv
  | notANumber => simp [unpackedValue] at hv
  | zero s =>
    have hx : x = 0 := by simpa [unpackedValue] using hv.symm
    subst x
    simp [wordValue, Float.Model.UnpackedFloat.pack, unpack_packedZero, unpackedValue]
  | finite s m e hm =>
    have hx : x = (s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
      simpa [unpackedValue] using hv.symm
    rw [hx] at hr
    have he := canonical_exponent_le hSF hmax s m e hm hc hr
    unfold wordValue
    rw [unpack_pack_finite S s m e hm hc he]
    exact hv

end FP.Native
