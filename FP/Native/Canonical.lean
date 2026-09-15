import FP.Native.Normalize

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

/-- Conditions on unpacked values needed by native packing. -/
def Canonical (S : Float.Model.Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ m e _ => m < 2 ^ S.mantissaBits ∧ S.minExponent ≤ e ∧
      (2 ^ S.mantissaBitsWithoutImplicit ≤ m ∨ e = S.minExponent)
  | _ => False

private theorem first_round_bounds {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℕ) (hm : 0 < m) (e : ℤ)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    let a := shiftToTargetExponent S m e .exact
    a.1.roundedMantissa ≤ 2 ^ S.mantissaBits ∧ S.minExponent ≤ a.2 ∧
      (2 ^ S.mantissaBitsWithoutImplicit ≤ a.1.roundedMantissa ∨ a.2 = S.minExponent) := by
  let t := S.targetExponent (totalExponent m e)
  let a := shiftToTargetExponent S m e .exact
  have hae : a.2 = t := shiftToExponent_exponent m e t he
  have ht : t = F.quantumExponent ((m : ℝ) * (2 : ℝ) ^ e) := hSF.targetExponent m hm e
  have har : (a.1.roundedMantissa : ℤ) = FP.IEEE.roundEven
      ((m : ℝ) * (2 : ℝ) ^ e / F.quantum ((m : ℝ) * (2 : ℝ) ^ e)) := by
    change ((shiftToExponent m e .exact t).1.roundedMantissa : ℤ) = _
    rw [shiftToExponent_round m e t he, ht]
    rfl
  have hbound : a.1.roundedMantissa ≤ 2 ^ S.mantissaBits := by
    have hh := F.rounded_mantissa_le ((m : ℝ) * (2 : ℝ) ^ e)
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
    have hmlo : (2 : ℝ) ^ m.log2 ≤ m := by
      exact_mod_cast ((Nat.le_log2 (by omega : m ≠ 0)).mp (le_refl m.log2))
    have hxlo : (2 : ℝ) ^ S.mantissaBitsWithoutImplicit ≤
        (m : ℝ) * (2 : ℝ) ^ e / (2 : ℝ) ^ t := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ t)]
      have hp : (2 : ℝ) ^ S.mantissaBitsWithoutImplicit * (2 : ℝ) ^ t =
          (2 : ℝ) ^ m.log2 * (2 : ℝ) ^ e := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ht']
        congr 1
        omega
      rw [hp]
      exact mul_le_mul_of_nonneg_right hmlo (by positivity)
    have herr := FP.IEEE.roundEven_error ((m : ℝ) * (2 : ℝ) ^ e / (2 : ℝ) ^ t)
    have har' := shiftToExponent_round m e t he
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
theorem roundWithAccuracy_canonical {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (hm : 0 < m) (e : ℤ)
    (he : e ≤ S.targetExponent (totalExponent m e)) :
    Canonical S (roundWithAccuracy S s m e .exact) := by
  let a := shiftToTargetExponent S m e .exact
  obtain ⟨hm', he', hl'⟩ := first_round_bounds hSF m hm e he
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

theorem round_canonical {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (e : ℤ) :
    Canonical S (Float.Model.UnpackedFloat.round S s m e) := by
  by_cases hz : m = 0
  · subst m
    simp [Float.Model.UnpackedFloat.round, decreaseExponent, Canonical]
  have hm : 0 < m := Nat.pos_of_ne_zero hz
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
  exact roundWithAccuracy_canonical hSF s d.1 hdm d.2 hde

theorem normalize_canonical {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (m : ℤ) (e : ℤ) (s : Sign) :
    Canonical S (Float.Model.UnpackedFloat.normalize S m e s) := by
  unfold Float.Model.UnpackedFloat.normalize
  split <;> try exact round_canonical hSF _ _ _
  trivial

theorem canonical_target (S : Float.Model.Format) (s : Sign) (m : ℕ) (e : ℤ)
    (hm : 0 < m) (hc : Canonical S (.finite s m e hm)) :
    S.targetExponent (totalExponent m e) = e := by
  obtain ⟨hu, hl, hn⟩ := hc
  have hlog : m.log2 < S.mantissaBits := (Nat.log2_lt hm.ne').mpr hu
  have hp := S.hm
  unfold Float.Model.Format.mantissaBits at hlog
  rcases hn with hn | rfl
  · have hg : S.mantissaBitsWithoutImplicit ≤ m.log2 := (Nat.le_log2 hm.ne').mpr hn
    unfold Float.Model.Format.targetExponent totalExponent Float.Model.Format.mantissaBits
    push_cast
    omega
  · unfold Float.Model.Format.targetExponent totalExponent Float.Model.Format.mantissaBits
    push_cast
    omega

theorem canonical_round_exact {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (hc : Canonical S (.finite s m e hm)) :
    F.roundFinite ((s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e) =
      (s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
  have ht := (hSF.targetExponent m hm e).symm.trans (canonical_target S s m e hm hc)
  have hpos : F.roundFinite ((m : ℝ) * (2 : ℝ) ^ e) = (m : ℝ) * (2 : ℝ) ^ e := by
    unfold FP.IEEE.Format.roundFinite FP.IEEE.Format.quantum
    rw [ht, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ) ^ e ≠ 0)]
    rw [show (m : ℝ) = ((m : ℤ) : ℝ) from rfl, FP.IEEE.roundEven_intCast]
  cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, roundFinite_neg, hpos]

end FP.Native
