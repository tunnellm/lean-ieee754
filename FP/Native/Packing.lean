import FP.Native.Canonical

noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

theorem minExponent_eq (S : Float.Model.Format) :
    S.minExponent = 1 - (S.exponentBias : ℤ) - S.mantissaBitsWithoutImplicit := by
  have hp : 1 ≤ 2 ^ (S.exponentBits - 1) := Nat.one_le_pow _ _ (by omega)
  unfold Float.Model.Format.minExponent Float.Model.Format.exponentBias Float.Model.Format.mantissaBits
  rw [Nat.cast_sub hp]
  push_cast
  ring

theorem exponent_capacity (S : Float.Model.Format) :
    2 ^ S.exponentBits = 2 * S.exponentBias + 2 := by
  have he := S.he
  have hp : 1 ≤ 2 ^ (S.exponentBits - 1) := Nat.one_le_pow _ _ (by omega)
  have heq : S.exponentBits = (S.exponentBits - 1) + 1 := by omega
  conv_lhs => rw [heq, pow_succ]
  unfold Float.Model.Format.exponentBias
  omega

theorem append_implicit (f : ℕ) (m : BitVec f) :
    (1#1 ++ m).toNat = 2 ^ f + m.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt]
  simp [Nat.shiftLeft_eq]

@[simp] theorem unpackSign_packComponents (S : Float.Model.Format) (s : Sign)
    (e : BitVec S.exponentBits) (m : BitVec S.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents S s e m) = s.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp [unpackSign, packComponents, BitVec.getLsbD_append, BitVec.getElem_append]

@[simp] theorem sign_of_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

@[simp] theorem unpack_packedZero (S : Float.Model.Format) (s : Sign) :
    unpack S (packedZero S s) = .zero s := by
  unfold Float.Model.UnpackedFloat.unpack packedZero
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
    sign_of_toBitVec]
  have hn : (0#S.exponentBits) ≠ -1#_ := by
    intro hh
    have := congrArg BitVec.toNat hh
    simp only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, BitVec.toNat_zero] at this
    have := S.he
    have hp : 2 ≤ 2 ^ S.exponentBits := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.exponentBits := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  simp [hn]

/-- Packing and unpacking a canonical finite datum is lossless if its exponent
fits. This is a theorem about Lean's actual native-model functions. -/
theorem unpack_pack_finite (S : Float.Model.Format) (s : Sign) (m : ℕ) (e : ℤ)
    (hm : 0 < m) (hc : Canonical S (.finite s m e hm))
    (hemax : e ≤ (S.exponentBias : ℤ) - S.mantissaBitsWithoutImplicit) :
    unpack S (pack S (.finite s m e hm)) = .finite s m e hm := by
  obtain ⟨hmu, hel, hlo⟩ := hc
  let b : ℕ := (e + S.exponentBias + S.mantissaBitsWithoutImplicit).toNat
  have hbpos : 1 ≤ e + (S.exponentBias : ℤ) + S.mantissaBitsWithoutImplicit := by
    rw [minExponent_eq] at hel
    omega
  have hbc : (b : ℤ) = e + S.exponentBias + S.mantissaBitsWithoutImplicit :=
    Int.toNat_of_nonneg (by omega)
  have hbu : b + 1 < 2 ^ S.exponentBits := by
    rw [exponent_capacity]
    omega
  have hbo : ¬ 2 ^ S.exponentBits ≤ b + 1 := by omega
  have hbe : (BitVec.ofNat S.exponentBits b).toNat = b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbez : (BitVec.ofNat S.exponentBits b) ≠ 0#_ := by
    intro hh
    have := congrArg BitVec.toNat hh
    rw [hbe] at this
    simp only [BitVec.toNat_zero] at this
    omega
  have hbei : (BitVec.ofNat S.exponentBits b) ≠ -1#_ := by
    intro hh
    have := congrArg BitVec.toNat hh
    rw [hbe] at this
    simp only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
    omega
  have hlogu : m.log2 < S.mantissaBits := (Nat.log2_lt hm.ne').mpr hmu
  by_cases hn : 2 ^ S.mantissaBitsWithoutImplicit ≤ m
  · have hlogl := (Nat.le_log2 hm.ne').mpr hn
    have hlog : m.log2 + 1 = S.mantissaBits := by
      unfold Float.Model.Format.mantissaBits at *
      omega
    have hmant : (1#1 ++ BitVec.ofNat S.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [append_implicit, BitVec.toNat_ofNat]
      have hpow : 2 ^ S.mantissaBits = 2 * 2 ^ S.mantissaBitsWithoutImplicit := by
        simp [Float.Model.Format.mantissaBits, pow_add]
      have hdiv : m / 2 ^ S.mantissaBitsWithoutImplicit = 1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      have hh := Nat.mod_add_div m (2 ^ S.mantissaBitsWithoutImplicit)
      rw [hdiv] at hh
      omega
    unfold Float.Model.UnpackedFloat.pack
    change unpack S (if 2 ^ S.exponentBits ≤ b + 1 then _ else if m.log2 + 1 = S.mantissaBits then _ else _) = _
    rw [if_neg hbo, if_pos hlog]
    unfold Float.Model.UnpackedFloat.unpack
    dsimp [b] at hbei hbez hbe
    simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
      hbei, if_false, hbez, sign_of_toBitVec, hbe, hmant]
    congr 1
    omega
  · have he : e = S.minExponent := hlo.resolve_left hn
    have hmlo : m < 2 ^ S.mantissaBitsWithoutImplicit := by omega
    have hlog : ¬ m.log2 + 1 = S.mantissaBits := by
      have := (Nat.log2_lt hm.ne').mpr hmlo
      unfold Float.Model.Format.mantissaBits
      omega
    have hmc : (BitVec.ofNat S.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmlo]
    have hmz : (BitVec.ofNat S.mantissaBitsWithoutImplicit m) ≠ 0#_ := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [hmc] at this
      simp only [BitVec.toNat_zero] at this
      omega
    have hei : (0#S.exponentBits) ≠ -1#_ := by
      intro hh
      have := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_zero, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
      have := exponent_capacity S
      omega
    unfold Float.Model.UnpackedFloat.pack
    change unpack S (if 2 ^ S.exponentBits ≤ b + 1 then _ else if m.log2 + 1 = S.mantissaBits then _ else _) = _
    rw [if_neg hbo, if_neg hlog]
    unfold Float.Model.UnpackedFloat.unpack
    dsimp [b] at hbei hbez hbe
    simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
      hei, if_false, if_true, hmz, hmc, sign_of_toBitVec, BitVec.toNat_zero]
    rw [he, minExponent_eq]
    push_cast
    ring_nf

end FP.Native
