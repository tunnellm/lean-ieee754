import FP.Native.Canonical

/-! Native rounding with arbitrary exact/inexact accuracy information.
Division and square root can use these results once their quotient/remainder or
integer-root constructions are proved to satisfy `Represents`. -/
noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

@[simp] theorem ofAccuracy_mantissa (m : ℕ) (a : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa = m := by
  cases a with
  | exact => rfl
  | inexact order => cases order <;> rfl

theorem Represents.mantissa_le {m : ℕ} {a : Accuracy} {x : ℝ}
    (h : Represents (ExtendedMantissa.ofMantissaAndAccuracy m a) x) : (m : ℝ) ≤ x := by
  have hf : ⌊x⌋ = (m : ℤ) := by simpa using h.floor
  have hl := Int.floor_le x
  rw [hf] at hl
  exact hl

theorem Represents.log {m : ℕ} (hm : 0 < m) {a : Accuracy} {x : ℝ}
    (h : Represents (ExtendedMantissa.ofMantissaAndAccuracy m a) x) :
    Int.log 2 x = (m.log2 : ℤ) := by
  have hlo : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : ⌊x⌋ = (m : ℤ) := by simpa using h.floor
  have hfn : ⌊x⌋₊ = m := by rw [← Int.floor_toNat, hf]; rfl
  rw [Int.log_of_one_le_right 2 (hlo.trans h.mantissa_le), hfn,
    Nat.log2_eq_log_two]

theorem FormatAgreement.targetExponent_represents {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ) (a : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m a) x) :
    S.targetExponent (totalExponent m e) = F.quantumExponent (x * (2 : ℝ) ^ e) := by
  have hp : 0 < x := lt_of_lt_of_le (by exact_mod_cast hm) hx.mantissa_le
  unfold FP.IEEE.Format.quantumExponent
  rw [abs_of_pos (mul_pos hp (by positivity)), log_mul_zpow hp e, hx.log hm]
  unfold Float.Model.Format.targetExponent totalExponent Float.Model.Format.mantissaBits
  rw [hSF.minExponent, hSF.fractionBits]
  push_cast
  omega

theorem shiftToExponent_round_of_represents (m : ℕ) (e t : ℤ) (a : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m a) x) (het : e ≤ t) :
    ((shiftToExponent m e a t).1.roundedMantissa : ℤ) =
      FP.IEEE.roundEven (x * (2 : ℝ) ^ e / (2 : ℝ) ^ t) := by
  have hn : ((t - e).toNat : ℤ) = t - e := Int.toNat_of_nonneg (by omega)
  have heq : x / (2 : ℝ) ^ (t - e).toNat = x * (2 : ℝ) ^ e / (2 : ℝ) ^ t := by
    rw [← zpow_natCast, hn, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
  have hh := (hx.shiftRight (t - e).toNat).roundedMantissa
  simpa only [shiftToExponent, heq] using hh

theorem shiftToExponent_exponent_of_accuracy (m : ℕ) (e t : ℤ) (a : Accuracy) (het : e ≤ t) :
    (shiftToExponent m e a t).2 = t := by
  simp only [shiftToExponent, Int.toNat_of_nonneg (sub_nonneg.mpr het)]
  omega

theorem roundWithAccuracy_positive_of_represents {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ) (accuracy : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m accuracy) x)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    unpackedValue (roundWithAccuracy S .positive m e accuracy) =
      some (F.roundFinite (x * (2 : ℝ) ^ e)) := by
  let t := S.targetExponent (totalExponent m e)
  let first := shiftToTargetExponent S m e accuracy
  have ht : t = F.quantumExponent (x * (2 : ℝ) ^ e) := hSF.targetExponent_represents m hm e accuracy x hx
  have hfe : first.2 = t := shiftToExponent_exponent_of_accuracy m e t accuracy he
  have hfr : (first.1.roundedMantissa : ℤ) =
      FP.IEEE.roundEven (x * (2 : ℝ) ^ e / F.quantum (x * (2 : ℝ) ^ e)) := by
    change ((shiftToExponent m e accuracy t).1.roundedMantissa : ℤ) = _
    rw [shiftToExponent_round_of_represents m e t accuracy x hx he, ht]
    rfl
  have hbound : first.1.roundedMantissa ≤ 2 ^ S.mantissaBits := by
    have hh := F.rounded_mantissa_le (x * (2 : ℝ) ^ e)
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
      F.roundFinite (x * (2 : ℝ) ^ e) := by
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

private theorem first_round_bounds_of_represents {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ) (accuracy : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m accuracy) x)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    let a := shiftToTargetExponent S m e accuracy
    a.1.roundedMantissa ≤ 2 ^ S.mantissaBits ∧ S.minExponent ≤ a.2 ∧
      (2 ^ S.mantissaBitsWithoutImplicit ≤ a.1.roundedMantissa ∨ a.2 = S.minExponent) := by
  let t := S.targetExponent (totalExponent m e)
  let a := shiftToTargetExponent S m e accuracy
  have hae : a.2 = t := shiftToExponent_exponent_of_accuracy m e t accuracy he
  have ht : t = F.quantumExponent (x * (2 : ℝ) ^ e) := hSF.targetExponent_represents m hm e accuracy x hx
  have har : (a.1.roundedMantissa : ℤ) = FP.IEEE.roundEven
      (x * (2 : ℝ) ^ e / F.quantum (x * (2 : ℝ) ^ e)) := by
    change ((shiftToExponent m e accuracy t).1.roundedMantissa : ℤ) = _
    rw [shiftToExponent_round_of_represents m e t accuracy x hx he, ht]
    rfl
  have hbound : a.1.roundedMantissa ≤ 2 ^ S.mantissaBits := by
    have hh := F.rounded_mantissa_le (x * (2 : ℝ) ^ e)
    rw [← har] at hh
    have hh' : ((a.1.roundedMantissa : ℕ) : ℝ) ≤ (2 : ℝ) ^ F.precision := by simpa using hh
    have hp : S.mantissaBits = F.precision := by
      simp [Float.Model.Format.mantissaBits, FP.IEEE.Format.precision, hSF.fractionBits, Nat.add_comm]
    rw [hp]
    exact_mod_cast hh'
  have hmin : S.minExponent ≤ a.2 := by rw [hae]; exact le_max_right _ _
  refine ⟨hbound, hmin, ?_⟩
  change (2 ^ S.mantissaBitsWithoutImplicit ≤ a.1.roundedMantissa ∨ a.2 = S.minExponent)
  by_cases heq : a.2 = S.minExponent
  · exact Or.inr heq
  · left
    have ht' : t = (m.log2 : ℤ) + e - S.mantissaBitsWithoutImplicit := by
      have hne : t ≠ S.minExponent := by simpa only [hae] using heq
      dsimp [t, Float.Model.Format.targetExponent, totalExponent, Float.Model.Format.mantissaBits] at hne ⊢
      omega
    have hmlo : (2 : ℝ) ^ m.log2 ≤ x := by
      have hl : (2 : ℝ) ^ m.log2 ≤ m := by
        exact_mod_cast ((Nat.le_log2 (by omega : m ≠ 0)).mp (le_refl m.log2))
      exact hl.trans hx.mantissa_le
    have hxlo : (2 : ℝ) ^ S.mantissaBitsWithoutImplicit ≤
        x * (2 : ℝ) ^ e / (2 : ℝ) ^ t := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ t)]
      have hp : (2 : ℝ) ^ S.mantissaBitsWithoutImplicit * (2 : ℝ) ^ t =
          (2 : ℝ) ^ m.log2 * (2 : ℝ) ^ e := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ht']
        congr 1
        omega
      rw [hp]
      exact mul_le_mul_of_nonneg_right hmlo (by positivity)
    have herr := FP.IEEE.roundEven_error (x * (2 : ℝ) ^ e / (2 : ℝ) ^ t)
    have har' := shiftToExponent_round_of_represents m e t accuracy x hx he
    change (a.1.roundedMantissa : ℤ) = _ at har'
    rw [← har'] at herr
    have hcast : ((a.1.roundedMantissa : ℕ) : ℝ) + 1 / 2 ≥ (2 : ℝ) ^ S.mantissaBitsWithoutImplicit := by
      have := (abs_le.mp herr).1
      push_cast at this
      linarith
    by_contra hh
    have hi : a.1.roundedMantissa + 1 ≤ 2 ^ S.mantissaBitsWithoutImplicit := by omega
    have hir : (a.1.roundedMantissa : ℝ) + 1 ≤ (2 : ℝ) ^ S.mantissaBitsWithoutImplicit := by exact_mod_cast hi
    linarith

/-- Native rounding produces a canonical unpacked result. -/
theorem roundWithAccuracy_canonical_of_represents {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (hm : 0 < m) (e : ℤ) (accuracy : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m accuracy) x)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    Canonical S (roundWithAccuracy S s m e accuracy) := by
  let a := shiftToTargetExponent S m e accuracy
  obtain ⟨hm', he', hl'⟩ := first_round_bounds_of_represents hSF m hm e accuracy x hx he
  change a.1.roundedMantissa ≤ _ at hm'
  change S.minExponent ≤ a.2 at he'
  change (2 ^ S.mantissaBitsWithoutImplicit ≤ a.1.roundedMantissa ∨ a.2 = S.minExponent) at hl'
  rcases hm'.lt_or_eq with hlt | heq
  · have hlog : a.1.roundedMantissa.log2 < S.mantissaBits := by
      by_cases hz : a.1.roundedMantissa = 0
      · rw [hz]; simp [Float.Model.Format.mantissaBits]
      · exact (Nat.log2_lt hz).mpr hlt
    have htarget : S.targetExponent (totalExponent a.1.roundedMantissa a.2) ≤ a.2 := by
      unfold Float.Model.Format.targetExponent totalExponent
      omega
    have hshift : (S.targetExponent (totalExponent a.1.roundedMantissa a.2) - a.2).toNat = 0 := by omega
    unfold roundWithAccuracy
    change Canonical S (if h : (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).1.mantissa = 0
      then .zero s else .finite s
        (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).1.mantissa
        (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).2 (Nat.pos_of_ne_zero h))
    simp only [shiftToTargetExponent, shiftToExponent, hshift]
    change Canonical S (if h : a.1.roundedMantissa = 0 then .zero s
      else .finite s a.1.roundedMantissa (a.2 + 0) (Nat.pos_of_ne_zero h))
    split_ifs <;> simp only [Canonical, add_zero]
    exact ⟨hlt, he', hl'⟩
  · have ht : S.targetExponent (totalExponent (2 ^ S.mantissaBits) a.2) = a.2 + 1 := by
      simp only [Float.Model.Format.targetExponent, totalExponent, Nat.log2_two_pow]
      omega
    have hdiv : 2 ^ S.mantissaBits / 2 = 2 ^ S.mantissaBitsWithoutImplicit := by
      simp [Float.Model.Format.mantissaBits, pow_add]
    unfold roundWithAccuracy
    change Canonical S (if h : (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).1.mantissa = 0
      then .zero s else .finite s
        (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).1.mantissa
        (shiftToTargetExponent S a.1.roundedMantissa a.2 .exact).2 (Nat.pos_of_ne_zero h))
    rw [heq]
    simp only [shiftToTargetExponent, ht, shiftToExponent, show (a.2 + 1 - a.2).toNat = 1 by omega]
    change Canonical S (if h : 2 ^ S.mantissaBits / 2 = 0 then .zero s
      else .finite s (2 ^ S.mantissaBits / 2) (a.2 + 1) (Nat.pos_of_ne_zero h))
    rw [hdiv]
    simp only [Nat.ne_of_gt (by positivity : 0 < 2 ^ S.mantissaBitsWithoutImplicit), Canonical]
    refine ⟨?_, by omega, Or.inl le_rfl⟩
    simp [Float.Model.Format.mantissaBits, pow_add]

/-- Signed native rounding for arbitrary represented fractional input. -/
theorem roundWithAccuracy_value_of_represents {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (hm : 0 < m) (e : ℤ)
    (accuracy : Accuracy) (x : ℝ)
    (hx : Represents (ExtendedMantissa.ofMantissaAndAccuracy m accuracy) x)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    unpackedValue (roundWithAccuracy S s m e accuracy) =
      some (F.roundFinite ((match s with | .positive => x | .negative => -x) * (2 : ℝ) ^ e)) := by
  cases s with
  | positive => exact roundWithAccuracy_positive_of_represents hSF m hm e accuracy x hx he
  | negative =>
    have hn : unpackedValue (roundWithAccuracy S .negative m e accuracy) =
        (unpackedValue (roundWithAccuracy S .positive m e accuracy)).map (fun y => -y) := by
      unfold roundWithAccuracy
      dsimp only
      split_ifs <;> simp [unpackedValue, Sign.apply]
    rw [hn, roundWithAccuracy_positive_of_represents hSF m hm e accuracy x hx he]
    simp [neg_mul]

end FP.Native
