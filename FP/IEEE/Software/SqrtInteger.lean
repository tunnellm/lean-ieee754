import FP.IEEE.Software.IntegerRound
import FP.IEEE.Spec.RealRounding
import Mathlib.Data.Nat.Sqrt

/-! Square-root rounding using integer square root and exact squared-midpoint tests. -/
namespace FP.IEEE.Software

def sqrtFloor (q : ℚ) : ℕ := Nat.sqrt ⌊q⌋₊

theorem sqrtFloor_bounds (q : ℚ) (hq : 0 ≤ q) :
    (sqrtFloor q : ℝ) ≤ Real.sqrt (q : ℝ) ∧ Real.sqrt (q : ℝ) < sqrtFloor q + 1 := by
  have hf : (⌊q⌋₊ : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.floor_le hq
  have hfu : (q : ℝ) < (⌊q⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one q
  have hl : (sqrtFloor q : ℝ)^2 ≤ (⌊q⌋₊ : ℝ) := by
    exact_mod_cast Nat.sqrt_le' ⌊q⌋₊
  have hu : (⌊q⌋₊ : ℝ) + 1 ≤ ((sqrtFloor q : ℝ) + 1)^2 := by
    have h := Nat.lt_succ_sqrt' ⌊q⌋₊
    have h' : ⌊q⌋₊ + 1 ≤ (sqrtFloor q + 1)^2 := h
    exact_mod_cast h'
  have hs := Real.sq_sqrt (show 0 ≤ (q : ℝ) by exact_mod_cast hq)
  have hn := Real.sqrt_nonneg (q : ℝ)
  have hk : (0 : ℝ) ≤ sqrtFloor q := by positivity
  constructor <;> nlinarith

def sqrtRoundInt (mode : RoundingMode) (q : ℚ) : ℤ :=
  let k : ℤ := sqrtFloor q
  match mode with
  | .towardNegative | .towardZero => k
  | .towardPositive => if (k : ℚ)^2 = q then k else k + 1
  | .nearestEven =>
    if q < ((k : ℚ) + 1/2)^2 then k
    else if ((k : ℚ) + 1/2)^2 < q then k + 1
    else k + k % 2
  | .nearestAway => if q < ((k : ℚ) + 1/2)^2 then k else k + 1

/-- Correct for irrational square roots as well as exact squares. -/
theorem sqrtRoundInt_spec (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    sqrtRoundInt mode q = Spec.roundInteger mode (Real.sqrt (q : ℝ)) := by
  let k : ℤ := sqrtFloor q
  let s := Real.sqrt (q : ℝ)
  have hb := sqrtFloor_bounds q hq
  have hn : 0 ≤ s := Real.sqrt_nonneg _
  have hk : (0 : ℝ) ≤ k := by dsimp [k]; positivity
  have hs : s^2 = (q : ℝ) := Real.sq_sqrt (by exact_mod_cast hq)
  have hf : ⌊s⌋ = k := Int.floor_eq_iff.mpr (by simpa [s, k] using hb)
  have he : (k : ℚ)^2 = q ↔ s = (k : ℝ) := by
    have hc : (k : ℚ)^2 = q ↔ (k : ℝ)^2 = (q : ℝ) := by norm_cast
    rw [hc]; constructor <;> intro h <;> nlinarith
  have hl : q < ((k : ℚ) + 1/2)^2 ↔ s - k < 1/2 := by
    have hc : q < ((k : ℚ) + 1/2)^2 ↔ (q : ℝ) < ((k : ℝ) + 1/2)^2 := by
      have h := (Rat.cast_lt (K := ℝ) (p := q) (q := ((k : ℚ) + 1/2)^2)).symm
      push_cast at h
      exact h
    rw [hc]; constructor <;> intro h <;> nlinarith
  have hu : ((k : ℚ) + 1/2)^2 < q ↔ 1/2 < s - k := by
    have hc : ((k : ℚ) + 1/2)^2 < q ↔ ((k : ℝ) + 1/2)^2 < (q : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ) (p := ((k : ℚ) + 1/2)^2) (q := q)).symm
      push_cast at h
      exact h
    rw [hc]; constructor <;> intro h <;> nlinarith
  have hc : ⌈s⌉ = if (k : ℚ)^2 = q then k else k + 1 := by
    split_ifs with h
    · rw [he] at h
      simp [h]
    · apply Int.ceil_eq_iff.mpr
      have hne := mt he.mpr h
      have hb' : (k : ℝ) ≤ s ∧ s < (k : ℝ) + 1 := by simpa [s, k] using hb
      have hlt : (k : ℝ) < s := lt_of_le_of_ne hb'.1 (Ne.symm hne)
      push_cast
      constructor <;> linarith
  change sqrtRoundInt mode q = Spec.roundInteger mode s
  cases mode <;> simp only [sqrtRoundInt, Spec.roundInteger, roundEven, hf, hc,
    show (sqrtFloor q : ℤ) = k from rfl, hl, hu, not_lt.mpr hn, if_false]
  split_ifs <;> rfl
end FP.IEEE.Software
