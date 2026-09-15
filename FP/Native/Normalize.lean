import FP.Native.Exponent
import FP.IEEE.Representation

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

/-- Mathematical value of a finite unpacked native float. Exceptional values
are deliberately returned as `none`. -/
def unpackedValue : UnpackedFloat → Option ℝ
  | .zero _ => some 0
  | .finite s m e _ => some ((s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e)
  | _ => none

/-- A bounded rounded mantissa needs at most one carry shift; that shift is exact. -/
theorem carry_shift_exact (S : Float.Model.Format) (m : ℕ) (e : ℤ)
    (hm : m ≤ 2 ^ S.mantissaBits) (he : S.minExponent ≤ e) :
    (((shiftToTargetExponent S m e .exact).1.mantissa : ℕ) : ℝ) *
      (2 : ℝ) ^ (shiftToTargetExponent S m e .exact).2 = (m : ℝ) * (2 : ℝ) ^ e := by
  rcases hm.lt_or_eq with hm | rfl
  · have hl : m.log2 < S.mantissaBits := by
      by_cases hz : m = 0
      · subst m
        simp [Float.Model.Format.mantissaBits]
      · exact (Nat.log2_lt hz).mpr hm
    have ht : S.targetExponent (totalExponent m e) ≤ e := by
      unfold Float.Model.Format.targetExponent totalExponent
      omega
    have hz : (S.targetExponent (totalExponent m e) - e).toNat = 0 := by omega
    simp [shiftToTargetExponent, shiftToExponent, hz,
      HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy]
  · have ht : S.targetExponent (totalExponent (2 ^ S.mantissaBits) e) = e + 1 := by
      simp only [Float.Model.Format.targetExponent, totalExponent, Nat.log2_two_pow]
      omega
    have hdiv : 2 ^ S.mantissaBits / 2 = 2 ^ S.mantissaBitsWithoutImplicit := by
      simp [Float.Model.Format.mantissaBits, pow_succ, pow_add]
    simp only [shiftToTargetExponent, ht, shiftToExponent,
      show (e + 1 - e).toNat = 1 by omega]
    change ((2 ^ S.mantissaBits / 2 : ℕ) : ℝ) * (2 : ℝ) ^ (e + 1) = _
    rw [hdiv]
    push_cast
    simp [Float.Model.Format.mantissaBits, pow_add, zpow_add₀]
    ring

/-- Real value of the native rounding operation, when its initial exponent does
not exceed the selected target. This is the precondition used by multiplication;
native `round` arranges it for normalization after addition. -/
theorem roundWithAccuracy_positive {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    unpackedValue (roundWithAccuracy S .positive m e .exact) =
      some (F.roundFinite ((m : ℝ) * (2 : ℝ) ^ e)) := by
  let t := S.targetExponent (totalExponent m e)
  let first := shiftToTargetExponent S m e .exact
  have ht : t = F.quantumExponent ((m : ℝ) * (2 : ℝ) ^ e) := hSF.targetExponent m hm e
  have hfe : first.2 = t := shiftToExponent_exponent m e t he
  have hfr : (first.1.roundedMantissa : ℤ) =
      FP.IEEE.roundEven ((m : ℝ) * (2 : ℝ) ^ e / F.quantum ((m : ℝ) * (2 : ℝ) ^ e)) := by
    change ((shiftToExponent m e .exact t).1.roundedMantissa : ℤ) = _
    rw [shiftToExponent_round m e t he, ht]
    rfl
  have hbound : first.1.roundedMantissa ≤ 2 ^ S.mantissaBits := by
    have hh := F.rounded_mantissa_le ((m : ℝ) * (2 : ℝ) ^ e)
    rw [← hfr] at hh
    have hh' : ((first.1.roundedMantissa : ℕ) : ℝ) ≤ (2 : ℝ) ^ F.precision := by
      simpa using hh
    have hp : S.mantissaBits = F.precision := by
      simp [Float.Model.Format.mantissaBits, FP.IEEE.Format.precision, hSF.fractionBits, Nat.add_comm]
    rw [hp]
    exact_mod_cast hh'
  have hmin : S.minExponent ≤ first.2 := by
    rw [hfe]
    exact le_max_right _ _
  have hc := carry_shift_exact S first.1.roundedMantissa first.2 hbound hmin
  have hr : ((first.1.roundedMantissa : ℕ) : ℝ) * (2 : ℝ) ^ first.2 =
      F.roundFinite ((m : ℝ) * (2 : ℝ) ^ e) := by
    unfold FP.IEEE.Format.roundFinite
    rw [hfe]
    have hcast := congrArg (fun k : ℤ => (k : ℝ)) hfr
    simp only [Int.cast_natCast] at hcast
    rw [hcast, ht]
    rfl
  unfold roundWithAccuracy
  change unpackedValue (if h : (shiftToTargetExponent S first.1.roundedMantissa first.2 .exact).1.mantissa = 0
    then .zero .positive else .finite .positive _ _ (Nat.pos_of_ne_zero h)) = _
  split_ifs with hz
  · simp only [unpackedValue]
    rw [hz] at hc
    simp only [Nat.cast_zero, zero_mul] at hc
    exact congrArg some (hc.trans hr)
  · simp only [unpackedValue, Sign.apply, Int.cast_natCast]
    exact congrArg some (hc.trans hr)

@[simp] theorem roundFinite_neg (F : FP.IEEE.Format) (x : ℝ) :
    F.roundFinite (-x) = -F.roundFinite x := by
  have hq : F.quantum (-x) = F.quantum x := by
    simp [FP.IEEE.Format.quantum, FP.IEEE.Format.quantumExponent]
  simp [FP.IEEE.Format.roundFinite, hq, neg_div, roundEven_neg]

private theorem roundWithAccuracy_negative (S : Float.Model.Format) (m : ℕ) (e : ℤ) :
    unpackedValue (roundWithAccuracy S .negative m e .exact) =
      (unpackedValue (roundWithAccuracy S .positive m e .exact)).map (fun x => -x) := by
  unfold roundWithAccuracy
  dsimp only
  split_ifs <;> simp [unpackedValue, Sign.apply]

theorem roundWithAccuracy_value {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (hm : 0 < m) (e : ℤ)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    unpackedValue (roundWithAccuracy S s m e .exact) =
      some (F.roundFinite ((s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e)) := by
  cases s with
  | positive => simpa [Sign.apply] using roundWithAccuracy_positive hSF m hm e he
  | negative =>
    rw [roundWithAccuracy_negative, roundWithAccuracy_positive hSF m hm e he]
    simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, roundFinite_neg, Option.map_some]

@[simp] theorem shift_zero (n : ℕ) :
    (ExtendedMantissa.ofMantissaAndAccuracy 0 .exact >>> n) =
      ExtendedMantissa.ofMantissaAndAccuracy 0 .exact := by
  change n.repeat ExtendedMantissa.shiftRightOne _ = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.repeat, ih]
    rfl

@[simp] theorem roundWithAccuracy_zero (S : Float.Model.Format) (s : Sign) (e : ℤ) :
    roundWithAccuracy S s 0 e .exact = .zero s := by
  unfold roundWithAccuracy
  simp only [shiftToTargetExponent, shiftToExponent, shift_zero]
  simp only [show (ExtendedMantissa.ofMantissaAndAccuracy 0 .exact).roundedMantissa = 0 from rfl]
  simp only [shift_zero]
  rfl

theorem decreaseExponent_value (m : ℕ) (e t : ℤ) :
    ((decreaseExponent m e t).1 : ℝ) * (2 : ℝ) ^ (decreaseExponent m e t).2 =
      (m : ℝ) * (2 : ℝ) ^ e := by
  simp only [decreaseExponent, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

/-- Native normalization agrees with the real rounding function for every
nonzero positive dyadic input, without an initial exponent restriction. -/
theorem round_positive {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ) :
    unpackedValue (Float.Model.UnpackedFloat.round S .positive m e) =
      some (F.roundFinite ((m : ℝ) * (2 : ℝ) ^ e)) := by
  let t := S.targetExponent (totalExponent m e)
  let d := decreaseExponent m e t
  have hdm : 0 < d.1 := by dsimp [d, decreaseExponent]; rw [Nat.shiftLeft_eq]; positivity
  have hdv : (d.1 : ℝ) * (2 : ℝ) ^ d.2 = (m : ℝ) * (2 : ℝ) ^ e :=
    decreaseExponent_value m e t
  have hdt : S.targetExponent (totalExponent d.1 d.2) = t := by
    rw [hSF.targetExponent d.1 hdm d.2, hdv, ← hSF.targetExponent m hm e]
  have hde : d.2 ≤ S.targetExponent (totalExponent d.1 d.2) := by
    rw [hdt]
    dsimp [d, decreaseExponent]
    omega
  have hh := roundWithAccuracy_positive hSF d.1 hdm d.2 hde
  rw [hdv] at hh
  exact hh

/-- Signed native normalization agrees with the real specification, including zero. -/
theorem round_value {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (e : ℤ) :
    unpackedValue (Float.Model.UnpackedFloat.round S s m e) =
      some (F.roundFinite ((s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e)) := by
  by_cases hz : m = 0
  · subst m
    simp [Float.Model.UnpackedFloat.round, decreaseExponent, roundWithAccuracy_zero,
      unpackedValue, Sign.apply]
    cases s <;> simp
  · have hm : 0 < m := Nat.pos_of_ne_zero hz
    cases s with
    | positive => simpa [Sign.apply] using round_positive hSF m hm e
    | negative =>
      unfold Float.Model.UnpackedFloat.round
      rw [roundWithAccuracy_negative]
      change (unpackedValue (Float.Model.UnpackedFloat.round S .positive m e)).map _ = _
      rw [round_positive hSF m hm e]
      simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, roundFinite_neg, Option.map_some]

/-- Native signed-integer normalization, the final step in native addition. -/
theorem normalize_value {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℤ) (e : ℤ) (s : Sign) :
    unpackedValue (normalize S m e s) = some (F.roundFinite ((m : ℝ) * (2 : ℝ) ^ e)) := by
  unfold Float.Model.UnpackedFloat.normalize
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · rw [show compare m 0 = .lt from Int.compare_eq_lt.mpr hm, round_value hSF]
    simp [Sign.apply, Int.toNat_of_nonneg (by omega : 0 ≤ -m)]
  · simp [unpackedValue]
  · rw [show compare m 0 = .gt from Int.compare_eq_gt.mpr hm, round_value hSF]
    simp [Sign.apply, Int.toNat_of_nonneg hm.le]

end FP.Native
