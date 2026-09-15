import FP.Native.Rounding
import FP.IEEE.Format

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

/-- Agreement of the native format and the real specification's precision and
least subnormal exponent. -/
structure FormatAgreement (S : Float.Model.Format) (F : FP.IEEE.Format) : Prop where
  fractionBits : S.mantissaBitsWithoutImplicit = F.fractionBits
  minExponent : S.minExponent = F.emin - F.fractionBits

theorem binary32_agreement : FormatAgreement Float.Model.Format.binary32 FP.IEEE.binary32 := by
  constructor <;> norm_num [Float.Model.Format.minExponent, Float.Model.Format.mantissaBits,
    FP.IEEE.binary32]

theorem binary64_agreement : FormatAgreement Float.Model.Format.binary64 FP.IEEE.binary64 := by
  constructor <;> norm_num [Float.Model.Format.minExponent, Float.Model.Format.mantissaBits,
    FP.IEEE.binary64]

/-- Integer logarithms commute with exact power-of-two scaling. -/
theorem log_mul_zpow {x : ℝ} (hx : 0 < x) (e : ℤ) :
    Int.log 2 (x * (2 : ℝ) ^ e) = Int.log 2 x + e := by
  have hp : 0 < (2 : ℝ) ^ e := by positivity
  have hxp := mul_pos hx hp
  have hlo := mul_le_mul_of_nonneg_right
    (Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) hx) hp.le
  have hhi := mul_lt_mul_of_pos_right
    (Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) x) hp
  have hl : Int.log 2 x + e ≤ Int.log 2 (x * (2 : ℝ) ^ e) := by
    apply (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hxp).mp
    simpa [zpow_add₀] using hlo
  have hh : Int.log 2 (x * (2 : ℝ) ^ e) < Int.log 2 x + e + 1 := by
    apply (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hxp).mp
    convert hhi using 1
    norm_num only [Nat.cast_ofNat]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  omega

theorem log_dyadic (m : ℕ) (hm : 0 < m) (e : ℤ) :
    Int.log 2 ((m : ℝ) * (2 : ℝ) ^ e) = (m.log2 : ℤ) + e := by
  rw [log_mul_zpow (by exact_mod_cast hm), Int.log_natCast, Nat.log2_eq_log_two]

theorem FormatAgreement.targetExponent {S : Float.Model.Format} {F : FP.IEEE.Format}
    (h : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ) :
    S.targetExponent (totalExponent m e) = F.quantumExponent ((m : ℝ) * (2 : ℝ) ^ e) := by
  have hp : 0 ≤ (m : ℝ) * (2 : ℝ) ^ e := by positivity
  unfold FP.IEEE.Format.quantumExponent
  rw [abs_of_nonneg hp, log_dyadic m hm e]
  unfold Float.Model.Format.targetExponent totalExponent Float.Model.Format.mantissaBits
  rw [h.minExponent, h.fractionBits]
  push_cast
  omega

/-- The first native rounding pass equals real nearest-even rounding on the
chosen dyadic lattice. -/
theorem shiftToExponent_round (m : ℕ) (e t : ℤ) (het : e ≤ t) :
    (((shiftToExponent m e .exact t).1.roundedMantissa : ℕ) : ℤ) =
      FP.IEEE.roundEven ((m : ℝ) * (2 : ℝ) ^ e / (2 : ℝ) ^ t) := by
  have hn : ((t - e).toNat : ℤ) = t - e := Int.toNat_of_nonneg (by omega)
  have heq : (m : ℝ) / (2 : ℝ) ^ (t - e).toNat =
      (m : ℝ) * (2 : ℝ) ^ e / (2 : ℝ) ^ t := by
    rw [← zpow_natCast, hn, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
  have hh := ((represents_exact m).shiftRight (t - e).toNat).roundedMantissa
  simpa only [shiftToExponent, heq] using hh

theorem shiftToExponent_exponent (m : ℕ) (e t : ℤ) (het : e ≤ t) :
    (shiftToExponent m e .exact t).2 = t := by
  simp only [shiftToExponent, Int.toNat_of_nonneg (sub_nonneg.mpr het)]
  omega

end FP.Native
