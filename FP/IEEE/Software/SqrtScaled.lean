import FP.IEEE.Software.SqrtInteger
import FP.IEEE.Software.TotalRound

/-! Binary exponent selection and scaled square-root rounding. -/
namespace FP.IEEE.Software

theorem log_sqrt (q : ℚ) (hq : 0 ≤ q) :
    Int.log 2 |Real.sqrt (q : ℝ)| = Int.log 2 q / 2 := by
  by_cases hz : q = 0
  · subst q; simp
  have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
  have hpR : (0 : ℝ) < q := by exact_mod_cast hp
  let l := Int.log 2 q / 2
  have hs := Real.sq_sqrt hpR.le
  have hsp := Real.sqrt_pos.mpr hpR
  have hl : (2 : ℝ)^(2*l) ≤ (q : ℝ) := by
    have h1 : (2 : ℝ)^(2*l) ≤ (2 : ℝ)^Int.log 2 q :=
      zpow_le_zpow_right₀ (by norm_num) (by dsimp [l]; omega)
    have h2 : (2 : ℝ)^Int.log 2 q ≤ (q : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) hp)
      simpa only [Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_ofNat] using h
    exact h1.trans h2
  have hu : (q : ℝ) < (2 : ℝ)^(2*(l+1)) := by
    have h1 : (q : ℝ) < (2 : ℝ)^(Int.log 2 q + 1) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr (Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) q)
      simpa only [Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_ofNat] using h
    exact h1.trans_le (zpow_le_zpow_right₀ (by norm_num) (by dsimp [l]; omega))
  have pow2 (e : ℤ) : (2 : ℝ)^(2*e) = ((2 : ℝ)^e)^2 := by
    rw [mul_comm, zpow_mul]; simp
  rw [pow2] at hl hu
  have hlo : (2 : ℝ)^l ≤ Real.sqrt (q : ℝ) := by
    have : (0 : ℝ) < 2^l := by positivity
    nlinarith
  have hhi : Real.sqrt (q : ℝ) < (2 : ℝ)^(l+1) := by
    have : (0 : ℝ) < 2^(l+1) := by positivity
    nlinarith
  rw [abs_of_pos hsp]
  have ha := (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hsp).mp hlo
  have hb := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hsp).mp hhi
  change _ = l
  omega

def sqrtAt (mode : RoundingMode) (q : ℚ) (e : ℤ) : ℚ :=
  let h := (2 : ℚ)^e
  (sqrtRoundInt mode (q / h^2) : ℚ) * h

theorem sqrtAt_cast (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) (e : ℤ) :
    (sqrtAt mode q e : ℝ) =
      (Spec.roundInteger mode (Real.sqrt (q : ℝ) / (2 : ℝ)^e) : ℝ) * (2 : ℝ)^e := by
  unfold sqrtAt
  push_cast
  rw [sqrtRoundInt_spec mode _ (div_nonneg hq (sq_nonneg _))]
  have he : Real.sqrt ((q / ((2 : ℚ)^e)^2 : ℚ) : ℝ) = Real.sqrt (q : ℝ) / (2 : ℝ)^e := by
    push_cast
    rw [Real.sqrt_div (by exact_mod_cast hq), Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  rw [he]

def sqrtScaled (F : Format) (mode : RoundingMode) (q : ℚ) : ℚ :=
  sqrtAt mode q (max F.emin (Int.log 2 q / 2) - F.fractionBits)

def sqrtPrecision (F : Format) (mode : RoundingMode) (q : ℚ) : ℚ :=
  sqrtAt mode q (Int.log 2 q / 2 - F.fractionBits)

theorem sqrtScaled_cast (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    (sqrtScaled F mode q : ℝ) = Spec.roundWithMode F mode (Real.sqrt (q : ℝ)) := by
  rw [sqrtScaled, sqrtAt_cast mode q hq]
  simp only [Spec.roundWithMode, Format.quantum, Format.quantumExponent, log_sqrt q hq]

theorem sqrtPrecision_cast (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    (sqrtPrecision F mode q : ℝ) = Spec.precisionRoundWithMode F mode (Real.sqrt (q : ℝ)) := by
  rw [sqrtPrecision, sqrtAt_cast mode q hq]
  simp only [Spec.precisionRoundWithMode, log_sqrt q hq]
end FP.IEEE.Software
