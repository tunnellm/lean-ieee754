import FP.Native.Finite

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

theorem signed_decrease_value (s : Sign) (m : ℕ) (e t : ℤ) (ht : t ≤ e) :
    (s.apply ((decreaseExponent m e t).1 : ℤ) : ℝ) * (2 : ℝ) ^ t =
      (s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
  have he : (decreaseExponent m e t).2 = t := by
    simp only [decreaseExponent, Int.toNat_of_nonneg (sub_nonneg.mpr ht)]
    omega
  have hv := decreaseExponent_value m e t
  rw [he] at hv
  cases s <;> simp only [Sign.apply, Int.cast_neg, Int.cast_natCast, neg_mul, hv]

/-- Correctness of native unpacked addition, including cancellation and signed zeros. -/
theorem add_unpacked {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (a b : UnpackedFloat) (x y : ℝ)
    (ha : Canonical S a) (hb : Canonical S b)
    (hax : unpackedValue a = some x) (hby : unpackedValue b = some y) :
    Canonical S (UnpackedFloat.add S a b) ∧
      unpackedValue (UnpackedFloat.add S a b) = some (F.roundFinite (x + y)) := by
  cases a with
  | infinity s => simp [unpackedValue] at hax
  | notANumber => simp [unpackedValue] at hax
  | zero s =>
    have hx : x = 0 := by simpa [unpackedValue] using hax.symm
    subst x
    cases b with
    | infinity s' => simp [unpackedValue] at hby
    | notANumber => simp [unpackedValue] at hby
    | zero s' =>
      have hy : y = 0 := by simpa [unpackedValue] using hby.symm
      subst y
      simp only [UnpackedFloat.add]
      split_ifs <;> simp [Canonical, unpackedValue]
    | finite s' m e hm =>
      have hy : y = (s'.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
        simpa [unpackedValue] using hby.symm
      simp only [UnpackedFloat.add, zero_add]
      exact ⟨hb, by rw [hy, canonical_round_exact hSF s' m e hm hb]; rfl⟩
  | finite s m e hm =>
    have hx : x = (s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
      simpa [unpackedValue] using hax.symm
    cases b with
    | infinity s' => simp [unpackedValue] at hby
    | notANumber => simp [unpackedValue] at hby
    | zero s' =>
      have hy : y = 0 := by simpa [unpackedValue] using hby.symm
      subst y
      simp only [UnpackedFloat.add, add_zero]
      exact ⟨ha, by rw [hx, canonical_round_exact hSF s m e hm ha]; rfl⟩
    | finite s' m' e' hm' =>
      have hy : y = (s'.apply (m' : ℤ) : ℝ) * (2 : ℝ) ^ e' := by
        simpa [unpackedValue] using hby.symm
      simp only [UnpackedFloat.add]
      refine ⟨normalize_canonical hSF _ _ _, ?_⟩
      rw [normalize_value hSF]
      congr 2
      push_cast
      rw [add_mul, signed_decrease_value s m e (min e e') (min_le_left _ _),
        signed_decrease_value s' m' e' (min e e') (min_le_right _ _), hx, hy]

private theorem mul_exponent_le (S : Float.Model.Format)
    (s s' : Sign) (m m' : ℕ) (e e' : ℤ) (hm : 0 < m) (hm' : 0 < m')
    (ha : Canonical S (.finite s m e hm)) (hb : Canonical S (.finite s' m' e' hm')) :
    e + e' ≤ S.targetExponent (totalExponent (m * m') (e + e')) := by
  have hp : 0 < m * m' := Nat.mul_pos hm hm'
  by_cases hn : 2 ^ S.mantissaBitsWithoutImplicit ≤ m * m'
  · have hl := (Nat.le_log2 hp.ne').mpr hn
    unfold Float.Model.Format.targetExponent totalExponent Float.Model.Format.mantissaBits
    push_cast
    omega
  · have hna : ¬2 ^ S.mantissaBitsWithoutImplicit ≤ m := by
      intro hh
      have : m ≤ m * m' := Nat.le_mul_of_pos_right m hm'
      omega
    have hnb : ¬2 ^ S.mantissaBitsWithoutImplicit ≤ m' := by
      intro hh
      have : m' ≤ m * m' := Nat.le_mul_of_pos_left m' hm
      omega
    have hea := ha.2.2.resolve_left hna
    have heb := hb.2.2.resolve_left hnb
    have hmin : S.minExponent ≤ 0 := by
      rw [minExponent_eq]
      have := S.hm
      omega
    unfold Float.Model.Format.targetExponent
    omega

/-- Correctness of native unpacked multiplication for canonical finite operands. -/
theorem mul_unpacked {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (a b : UnpackedFloat) (x y : ℝ)
    (ha : Canonical S a) (hb : Canonical S b)
    (hax : unpackedValue a = some x) (hby : unpackedValue b = some y) :
    Canonical S (UnpackedFloat.mul S a b) ∧
      unpackedValue (UnpackedFloat.mul S a b) = some (F.roundFinite (x * y)) := by
  cases a with
  | infinity s => simp [unpackedValue] at hax
  | notANumber => simp [unpackedValue] at hax
  | zero s =>
    have hx : x = 0 := by simpa [unpackedValue] using hax.symm
    subst x
    cases b with
    | infinity s' => simp [unpackedValue] at hby
    | notANumber => simp [unpackedValue] at hby
    | zero s' => simp [UnpackedFloat.mul, Canonical, unpackedValue]
    | finite s' m e hm => simp [UnpackedFloat.mul, Canonical, unpackedValue]
  | finite s m e hm =>
    have hx : x = (s.apply (m : ℤ) : ℝ) * (2 : ℝ) ^ e := by
      simpa [unpackedValue] using hax.symm
    cases b with
    | infinity s' => simp [unpackedValue] at hby
    | notANumber => simp [unpackedValue] at hby
    | zero s' =>
      have hy : y = 0 := by simpa [unpackedValue] using hby.symm
      subst y
      simp [UnpackedFloat.mul, Canonical, unpackedValue]
    | finite s' m' e' hm' =>
      have hy : y = (s'.apply (m' : ℤ) : ℝ) * (2 : ℝ) ^ e' := by
        simpa [unpackedValue] using hby.symm
      have he := mul_exponent_le S s s' m m' e e' hm hm' ha hb
      simp only [UnpackedFloat.mul]
      refine ⟨roundWithAccuracy_canonical hSF _ _ (Nat.mul_pos hm hm') _ he, ?_⟩
      rw [roundWithAccuracy_value hSF _ _ (Nat.mul_pos hm hm') _ he, hx, hy]
      congr 2
      cases s <;> cases s' <;>
        simp [Sign.apply, zpow_add₀] <;> ring

/-- Native packed addition agrees with the specification whenever the exact
sum is below the nearest-even overflow threshold. Subnormal results are allowed. -/
theorem add_words {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (hmax : F.emax = (S.exponentBias : ℤ))
    (a b : BitVec S.numBits) (x y : ℝ)
    (hax : wordValue S a = some x) (hby : wordValue S b = some y)
    (hr : |x + y| < F.overflowThreshold) :
    wordValue S (pack S (UnpackedFloat.add S (unpack S a) (unpack S b))) = F.round? (x + y) := by
  obtain ⟨hc, hv⟩ := add_unpacked hSF (unpack S a) (unpack S b) x y
    (unpack_canonical S a x hax) (unpack_canonical S b y hby) hax hby
  rw [pack_value hSF hmax _ _ hc hv (F.roundFinite_representable hr)]
  simp only [FP.IEEE.Format.round?, if_pos hr]

theorem mul_words {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (hmax : F.emax = (S.exponentBias : ℤ))
    (a b : BitVec S.numBits) (x y : ℝ)
    (hax : wordValue S a = some x) (hby : wordValue S b = some y)
    (hr : |x * y| < F.overflowThreshold) :
    wordValue S (pack S (UnpackedFloat.mul S (unpack S a) (unpack S b))) = F.round? (x * y) := by
  obtain ⟨hc, hv⟩ := mul_unpacked hSF (unpack S a) (unpack S b) x y
    (unpack_canonical S a x hax) (unpack_canonical S b y hby) hax hby
  rw [pack_value hSF hmax _ _ hc hv (F.roundFinite_representable hr)]
  simp only [FP.IEEE.Format.round?, if_pos hr]

end FP.Native
