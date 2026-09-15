import FP.IEEE.Rounding
import Init.Data.Float.Model

/-! Relating Lean's native guard/round/sticky machinery to real nearest-even rounding. -/
noncomputable section
namespace FP.Native
open Float.Model.UnpackedFloat

/-- Exact meaning of the native mantissa and its round/sticky bits. -/
def Represents (em : ExtendedMantissa) (x : ℝ) : Prop :=
  if em.roundBit then
    if em.stickyBit then (em.mantissa : ℝ) + 1 / 2 < x ∧ x < em.mantissa + 1
    else x = em.mantissa + 1 / 2
  else
    if em.stickyBit then (em.mantissa : ℝ) < x ∧ x < em.mantissa + 1 / 2
    else x = em.mantissa

theorem represents_exact (m : ℕ) :
    Represents (ExtendedMantissa.ofMantissaAndAccuracy m .exact) m := by
  simp [Represents, ExtendedMantissa.ofMantissaAndAccuracy]

theorem Represents.floor {em : ExtendedMantissa} {x : ℝ} (h : Represents em x) :
    ⌊x⌋ = (em.mantissa : ℤ) := by
  apply Int.floor_eq_iff.mpr
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;> simp_all [Represents] <;> try constructor
  all_goals norm_num at *
  all_goals linarith

theorem Represents.roundedMantissa {em : ExtendedMantissa} {x : ℝ}
    (h : Represents em x) : (em.roundedMantissa : ℤ) = FP.IEEE.roundEven x := by
  have hf := h.floor
  unfold FP.IEEE.roundEven
  rw [hf]
  dsimp only
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;>
    simp_all only [Represents, Bool.false_eq_true, if_false, if_true,
      ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]
  all_goals push_cast
  all_goals split_ifs <;> try omega
  all_goals try linarith

theorem Represents.shiftRightOne {em : ExtendedMantissa} {x : ℝ}
    (h : Represents em x) : Represents em.shiftRightOne (x / 2) := by
  rcases em with ⟨m, r, s⟩
  have hm := Nat.mod_add_div m 2
  have hr : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hc : ((m % 2 : ℕ) : ℝ) + 2 * ((m / 2 : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast hm
  cases r <;> cases s <;> rcases hr with hr | hr <;>
    simp_all [Represents, ExtendedMantissa.shiftRightOne] <;>
    (try constructor) <;> norm_num at * <;> linarith

/-- Native repeated right shifts preserve the exact rounding information. -/
theorem Represents.shiftRight {em : ExtendedMantissa} {x : ℝ}
    (h : Represents em x) (n : ℕ) : Represents (em >>> n) (x / (2 : ℝ) ^ n) := by
  change Represents (n.repeat ExtendedMantissa.shiftRightOne em) _
  induction n with
  | zero => simpa [Nat.repeat] using h
  | succ n ih =>
    rw [Nat.repeat]
    have hh := ih.shiftRightOne
    simpa only [pow_succ, div_mul_eq_div_div] using hh

/-- The signed real specification rounds symmetrically, including midpoint ties. -/
theorem roundEven_neg (x : ℝ) : FP.IEEE.roundEven (-x) = -FP.IEEE.roundEven x := by
  by_cases hx : x = (⌊x⌋ : ℝ)
  · conv_lhs => rw [hx, ← Int.cast_neg, FP.IEEE.roundEven_intCast]
    conv_rhs => rw [hx, FP.IEEE.roundEven_intCast]
  · have hlo := Int.floor_le x
    have hhi := Int.lt_floor_add_one x
    have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne hlo (Ne.symm hx)
    have hf : ⌊-x⌋ = -⌊x⌋ - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hm := Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
    have hm' := Int.emod_lt_of_pos ⌊x⌋ (by norm_num : (0 : ℤ) < 2)
    have hn := Int.emod_nonneg (-⌊x⌋ - 1) (by norm_num : (2 : ℤ) ≠ 0)
    have hn' := Int.emod_lt_of_pos (-⌊x⌋ - 1) (by norm_num : (0 : ℤ) < 2)
    unfold FP.IEEE.roundEven
    rw [hf]
    dsimp only
    push_cast
    split_ifs <;> try omega
    all_goals linarith

end FP.Native
