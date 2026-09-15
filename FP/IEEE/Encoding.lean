import FP.IEEE.Representation

/-! Binary interchange bit fields and their exact finite real values.
All-ones exponents (infinities and NaNs) have no finite real projection.
Positive and negative zero both project to the real number zero.
-/
noncomputable section
namespace FP.IEEE

structure Interchange where
  format : Format
  exponentBits : ℕ
  bias : ℤ
  emin_eq : format.emin = 1 - bias
  emax_eq : format.emax = (2 : ℤ) ^ exponentBits - 2 - bias

def fp32 : Interchange := ⟨binary32, 8, 127, by norm_num [binary32], by norm_num [binary32]⟩
def fp64 : Interchange := ⟨binary64, 11, 1023, by norm_num [binary64], by norm_num [binary64]⟩

namespace Interchange

def width (I : Interchange) : ℕ := 1 + I.exponentBits + I.format.fractionBits
abbrev Word (I : Interchange) := BitVec I.width

def fraction (I : Interchange) (w : I.Word) : ℕ :=
  w.toNat % 2 ^ I.format.fractionBits

def exponent (I : Interchange) (w : I.Word) : ℕ :=
  (w.toNat / 2 ^ I.format.fractionBits) % 2 ^ I.exponentBits

def negative (I : Interchange) (w : I.Word) : Bool :=
  w.getLsbD (I.exponentBits + I.format.fractionBits)

/-- True exactly for zero, subnormal, or normal bit patterns. -/
def IsFinite (I : Interchange) (w : I.Word) : Prop :=
  I.exponent w ≠ 2 ^ I.exponentBits - 1

def mantissa (I : Interchange) (w : I.Word) : ℕ :=
  if I.exponent w = 0 then I.fraction w else 2 ^ I.format.fractionBits + I.fraction w

def scaleExponent (I : Interchange) (w : I.Word) : ℤ :=
  (if I.exponent w = 0 then I.format.emin else (I.exponent w : ℤ) - I.bias) -
    I.format.fractionBits

/-- For finite words this is their exact mathematical value. Use `decode?` when
finiteness is not known, to avoid assigning real values to exceptional words. -/
def value (I : Interchange) (w : I.Word) : ℝ :=
  (if I.negative w then -1 else 1) *
    ((I.mantissa w : ℝ) * (2 : ℝ) ^ I.scaleExponent w)

instance (I : Interchange) (w : I.Word) : Decidable (I.IsFinite w) :=
  inferInstanceAs (Decidable (_ ≠ _))

def decode? (I : Interchange) (w : I.Word) : Option ℝ :=
  if I.IsFinite w then some (I.value w) else none

theorem decode?_eq (I : Interchange) (w : I.Word) (hw : I.IsFinite w) :
    I.decode? w = some (I.value w) := by simp [decode?, hw]

/-- Every finite IEEE bit pattern decodes to a representable value. -/
theorem value_representable (I : Interchange) (w : I.Word) (hw : I.IsFinite w) :
    I.format.Representable (I.value w) := by
  have hf : I.fraction w < 2 ^ I.format.fractionBits := Nat.mod_lt _ (by positivity)
  have hexp : I.exponent w < 2 ^ I.exponentBits := Nat.mod_lt _ (by positivity)
  have hemax : I.exponent w ≤ 2 ^ I.exponentBits - 2 := by
    unfold IsFinite at hw
    omega
  have hm : I.mantissa w < 2 ^ I.format.precision := by
    unfold mantissa Format.precision
    rw [pow_succ]
    split_ifs <;> omega
  have hscale : I.format.emin - I.format.fractionBits ≤ I.scaleExponent w ∧
      I.scaleExponent w ≤ I.format.emax - I.format.fractionBits := by
    unfold scaleExponent
    split_ifs with h
    · exact ⟨le_rfl, sub_le_sub_right I.format.exponent_order _⟩
    · have hp : (1 : ℤ) ≤ I.exponent w := by exact_mod_cast (show 1 ≤ I.exponent w by omega)
      have he : (I.exponent w : ℤ) ≤ (2 : ℤ) ^ I.exponentBits - 2 := by
        have hh : I.exponent w + 2 ≤ 2 ^ I.exponentBits := by
          have hg : 2 ≤ 2 ^ I.exponentBits := by omega
          omega
        have hh' : (I.exponent w : ℤ) + 2 ≤ (2 : ℤ) ^ I.exponentBits := by exact_mod_cast hh
        omega
      rw [I.emin_eq, I.emax_eq]
      constructor <;> omega
  have hm' : (I.mantissa w : ℝ) < (2 : ℝ) ^ I.format.precision := by exact_mod_cast hm
  by_cases hn : I.negative w = true
  · refine ⟨-(I.mantissa w : ℤ), I.scaleExponent w, hscale.1, hscale.2, ?_, ?_⟩
    · simpa using hm'
    · simp [value, hn]
  · refine ⟨(I.mantissa w : ℤ), I.scaleExponent w, hscale.1, hscale.2, ?_, ?_⟩
    · simpa using hm'
    · simp [value, hn]

end Interchange

@[simp] theorem fp32_width : fp32.width = 32 := rfl
@[simp] theorem fp64_width : fp64.width = 64 := rfl

end FP.IEEE
