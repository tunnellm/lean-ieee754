import FP.Native.Packing
import FP.IEEE.Encoding

noncomputable section
open scoped Classical
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

/-- The real interpretation of a native packed word, excluding exceptional values. -/
def wordValue (S : Float.Model.Format) (w : BitVec S.numBits) : Option ℝ :=
  unpackedValue (unpack S w)

theorem unpack_canonical (S : Float.Model.Format) (w : BitVec S.numBits) (x : ℝ)
    (hx : wordValue S w = some x) : Canonical S (unpack S w) := by
  unfold wordValue Float.Model.UnpackedFloat.unpack at *
  dsimp only at *
  split_ifs at hx ⊢ with hi hz hm
  all_goals try { simp [unpackedValue] at hx }
  · trivial
  · have hmant := (unpackMantissa w).isLt
    have hp : 2 ^ S.mantissaBitsWithoutImplicit ≤ 2 ^ S.mantissaBits := by
      apply Nat.pow_le_pow_right (by norm_num)
      simp [Float.Model.Format.mantissaBits]
    simp only [Canonical, hm, BitVec.toNat_zero, Nat.cast_zero]
    have heq : (0 : ℤ) - (S.exponentBias + S.mantissaBitsWithoutImplicit) + 1 = S.minExponent := by
      rw [minExponent_eq]
      ring
    rw [heq]
    exact ⟨hmant.trans_le hp, le_rfl, Or.inr rfl⟩
  · have hmant := (unpackMantissa w).isLt
    have hepos : 0 < (unpackExponent w).toNat := by
      apply Nat.pos_of_ne_zero
      intro hh
      apply hm
      exact BitVec.eq_of_toNat_eq (by simpa using hh)
    simp only [Canonical, append_implicit]
    refine ⟨?_, ?_, Or.inl (by omega)⟩
    · simp only [Float.Model.Format.mantissaBits, pow_add, pow_one]
      omega
    · rw [minExponent_eq]
      have hcast : (1 : ℤ) ≤ (unpackExponent w).toNat := by exact_mod_cast hepos
      omega

/-- Field-level equality of our binary decoder and the native unpacker. -/
theorem unpack_mantissa_toNat (S : Float.Model.Format) (w : BitVec S.numBits) :
    (unpackMantissa w).toNat = w.toNat % 2 ^ S.mantissaBitsWithoutImplicit := by
  simp only [unpackMantissa, BitVec.toNat_cast, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  have := S.hm
  congr 2
  omega

theorem unpack_exponent_toNat (S : Float.Model.Format) (w : BitVec S.numBits) :
    (unpackExponent w).toNat = (w.toNat / 2 ^ S.mantissaBitsWithoutImplicit) % 2 ^ S.exponentBits := by
  simp only [unpackExponent, BitVec.toNat_cast, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have := S.he
  congr 2
  omega

theorem unpack_sign_zero_iff (S : Float.Model.Format) (w : BitVec S.numBits) :
    unpackSign w = 0#1 ↔ w.getLsbD (S.exponentBits + S.mantissaBitsWithoutImplicit) = false := by
  constructor
  · intro h
    have hh := congrArg (fun b : BitVec 1 => b.getLsbD 0) h
    simpa [unpackSign, Nat.add_comm] using hh
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst i
    simpa [unpackSign, Nat.add_comm] using h

private theorem sign_apply_cast (s : Sign) (m : ℤ) :
    (s.apply m : ℝ) = (if s = .negative then -1 else 1) * (m : ℝ) := by
  classical
  cases s <;> simp [Sign.apply]

/-- A bit-field formula for the native unpacker's real interpretation. -/
theorem wordValue_formula (S : Float.Model.Format) (w : BitVec S.numBits) :
    wordValue S w =
      if (unpackExponent w).toNat = 2 ^ S.exponentBits - 1 then none
      else some ((if w.getLsbD (S.exponentBits + S.mantissaBitsWithoutImplicit) then -1 else 1) *
        ((if (unpackExponent w).toNat = 0 then ((unpackMantissa w).toNat : ℝ)
          else (2 : ℝ) ^ S.mantissaBitsWithoutImplicit + (unpackMantissa w).toNat) *
          (2 : ℝ) ^ ((if (unpackExponent w).toNat = 0 then 1 - (S.exponentBias : ℤ)
            else ((unpackExponent w).toNat : ℤ) - S.exponentBias) - S.mantissaBitsWithoutImplicit))) := by
  classical
  have he0 : unpackExponent w = 0#_ ↔ (unpackExponent w).toNat = 0 := by
    rw [← BitVec.toNat_inj]; simp
  have hei : unpackExponent w = -1#_ ↔ (unpackExponent w).toNat = 2 ^ S.exponentBits - 1 := by
    rw [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
  have hsign : (Sign.ofBitVec (unpackSign w) = .negative) ↔
      w.getLsbD (S.exponentBits + S.mantissaBitsWithoutImplicit) = true := by
    unfold Sign.ofBitVec
    simp only [unpack_sign_zero_iff]
    cases w.getLsbD (S.exponentBits + S.mantissaBitsWithoutImplicit) <;> simp
  unfold wordValue Float.Model.UnpackedFloat.unpack
  dsimp only
  simp only [he0, hei]
  split_ifs with hi hz he hz'
  all_goals simp_all [unpackedValue, sign_apply_cast, sub_sub]
  all_goals ring_nf
  all_goals simp [Nat.shiftLeft_eq, add_comm]
  all_goals
    left
    have hh : 2 ^ S.mantissaBitsWithoutImplicit ||| (unpackMantissa w).toNat =
        2 ^ S.mantissaBitsWithoutImplicit + (unpackMantissa w).toNat := by
      simpa [BitVec.toNat_append, Nat.shiftLeft_eq] using append_implicit _ (unpackMantissa w)
    exact_mod_cast hh

theorem wordValue_binary32 (w : BitVec 32) :
    wordValue Float.Model.Format.binary32 w = FP.IEEE.fp32.decode? w := by
  rw [wordValue_formula, unpack_exponent_toNat, unpack_mantissa_toNat]
  simp only [FP.IEEE.Interchange.decode?, FP.IEEE.Interchange.IsFinite, FP.IEEE.Interchange.value,
    FP.IEEE.Interchange.exponent, FP.IEEE.Interchange.negative, FP.IEEE.Interchange.mantissa,
    FP.IEEE.Interchange.scaleExponent, FP.IEEE.Interchange.fraction]
  norm_num only [FP.IEEE.fp32, FP.IEEE.binary32, Float.Model.Format.exponentBias,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_ite, Nat.cast_add, Nat.cast_ofNat]
  split_ifs <;> first | contradiction | rfl

theorem wordValue_binary64 (w : BitVec 64) :
    wordValue Float.Model.Format.binary64 w = FP.IEEE.fp64.decode? w := by
  rw [wordValue_formula, unpack_exponent_toNat, unpack_mantissa_toNat]
  simp only [FP.IEEE.Interchange.decode?, FP.IEEE.Interchange.IsFinite, FP.IEEE.Interchange.value,
    FP.IEEE.Interchange.exponent, FP.IEEE.Interchange.negative, FP.IEEE.Interchange.mantissa,
    FP.IEEE.Interchange.scaleExponent, FP.IEEE.Interchange.fraction]
  norm_num only [FP.IEEE.fp64, FP.IEEE.binary64, Float.Model.Format.exponentBias,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
  simp only [Nat.cast_ite, Nat.cast_add, Nat.cast_ofNat]
  split_ifs <;> first | contradiction | rfl

end FP.Native
