import FP.IEEE.Encoding

/-! Lossless binary interchange fields. Unlike the finite real projection,
these functions preserve every encoding, including signed zeros and NaNs. -/
set_option backward.isDefEq.respectTransparency false

namespace FP.IEEE.Interchange

/-- Parameters needed by the total binary implementation. -/
class Valid (I : Interchange) : Prop where
  fraction_pos : 0 < I.format.fractionBits
  exponent_pos : 0 < I.exponentBits

instance : fp32.Valid := ⟨by decide, by decide⟩
instance : fp64.Valid := ⟨by decide, by decide⟩

structure Fields (I : Interchange) where
  negative : Bool
  exponent : BitVec I.exponentBits
  fraction : BitVec I.format.fractionBits
  deriving DecidableEq

namespace Fields

def pack {I : Interchange} (f : Fields I) : I.Word :=
  (BitVec.ofBool f.negative ++ f.exponent) ++ f.fraction

def unpack (I : Interchange) (w : I.Word) : Fields I :=
  ⟨I.negative w, w.extractLsb' I.format.fractionBits I.exponentBits,
    w.extractLsb' 0 I.format.fractionBits⟩

@[simp] theorem unpack_pack {I : Interchange} (f : Fields I) :
    unpack I f.pack = f := by
  cases f with
  | mk s e m =>
    simp only [unpack, pack, Interchange.negative]
    congr 1
    · simp [BitVec.getLsbD_append, BitVec.getElem_append, BitVec.getElem_ofBool]
    · rw [BitVec.extractLsb'_append_eq_of_le (Nat.le_refl _)]
      simp [BitVec.extractLsb'_append_eq_right]
    · exact BitVec.extractLsb'_append_eq_right

@[simp] theorem pack_unpack (I : Interchange) (w : I.Word) :
    (unpack I w).pack = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, unpack, Interchange.negative, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool]
  by_cases hm : i < I.format.fractionBits
  · simp [hm]
  · by_cases he : i - I.format.fractionBits < I.exponentBits
    · simp [hm, he, Nat.add_sub_of_le (Nat.le_of_not_gt hm)]
    · have hs : i = I.exponentBits + I.format.fractionBits := by
        change i < 1 + I.exponentBits + I.format.fractionBits at hi
        omega
      subst i
      simp

@[simp] theorem fraction_unpack (I : Interchange) (w : I.Word) :
    (unpack I w).fraction.toNat = I.fraction w := by
  simp [unpack, Interchange.fraction, BitVec.extractLsb'_toNat]

@[simp] theorem exponent_unpack (I : Interchange) (w : I.Word) :
    (unpack I w).exponent.toNat = I.exponent w := by
  simp [unpack, Interchange.exponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

@[simp] theorem negative_unpack (I : Interchange) (w : I.Word) :
    (unpack I w).negative = I.negative w := rfl

@[simp] theorem fraction_pack {I : Interchange} (f : Fields I) :
    I.fraction f.pack = f.fraction.toNat := by
  rw [← fraction_unpack, unpack_pack]

@[simp] theorem exponent_pack {I : Interchange} (f : Fields I) :
    I.exponent f.pack = f.exponent.toNat := by
  rw [← exponent_unpack, unpack_pack]

@[simp] theorem negative_pack {I : Interchange} (f : Fields I) :
    I.negative f.pack = f.negative := by
  rw [← negative_unpack, unpack_pack]

@[simp] theorem isFinite_pack {I : Interchange} (f : Fields I) :
    I.IsFinite f.pack ↔ f.exponent ≠ BitVec.allOnes I.exponentBits := by
  simp [IsFinite, ← BitVec.toNat_inj]

/-- Exact rational value of finite fields. Exceptional encodings must be
filtered by the total datum's `toRat?` interface. -/
def rationalValue {I : Interchange} (f : Fields I) : ℚ :=
  (if f.negative then -1 else 1) *
    ((if f.exponent = 0 then f.fraction.toNat else
      2 ^ I.format.fractionBits + f.fraction.toNat : ℕ) : ℚ) *
    (2 : ℚ) ^ ((if f.exponent = 0 then I.format.emin else
      (f.exponent.toNat : ℤ) - I.bias) - I.format.fractionBits)

theorem rationalValue_cast {I : Interchange} (f : Fields I) :
    (f.rationalValue : ℝ) = I.value f.pack := by
  simp only [rationalValue, value, mantissa, scaleExponent,
    fraction_pack, exponent_pack, negative_pack]
  have hz : f.exponent.toNat = 0 ↔ f.exponent = 0 := by
    rw [← BitVec.toNat_inj]; rfl
  simp only [hz]
  push_cast
  split_ifs <;> push_cast <;> ring

/-- Changing only the sign never changes an exponent or fraction bit. -/
def withSign {I : Interchange} (f : Fields I) (s : Bool) : Fields I :=
  { f with negative := s }

@[simp] theorem withSign_withSign {I : Interchange} (f : Fields I) (s t : Bool) :
    (f.withSign s).withSign t = f.withSign t := rfl

end Fields
end FP.IEEE.Interchange
