import FP.Basic
import Mathlib.Data.Int.Log

/-! Exact round-to-nearest, ties-to-even, over the reals. -/
noncomputable section
namespace FP.IEEE

/-- Round to the nearest integer, selecting the even integer at a midpoint. -/
def roundEven (x : ℝ) : ℤ :=
  let k := ⌊x⌋
  if x - k < 1 / 2 then k
  else if 1 / 2 < x - k then k + 1
  else k + k % 2

theorem roundEven_error (x : ℝ) : |(roundEven x : ℝ) - x| ≤ 1 / 2 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  have hm0 : (0 : ℝ) ≤ (⌊x⌋ % 2 : ℤ) := by exact_mod_cast Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
  have hm1 : ((⌊x⌋ % 2 : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast (show ⌊x⌋ % 2 ≤ 1 by omega)
  unfold roundEven
  dsimp only
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

@[simp] theorem roundEven_intCast (k : ℤ) : roundEven (k : ℝ) = k := by
  simp [roundEven]

@[simp] theorem roundEven_zero : roundEven 0 = 0 := by
  simpa using roundEven_intCast 0

/-- Both choices at a midpoint are resolved by the parity of the lower integer. -/
theorem roundEven_midpoint (k : ℤ) :
    roundEven ((k : ℝ) + 1 / 2) = k + k % 2 := by
  have hf : ⌊(k : ℝ) + 1 / 2⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  unfold roundEven
  rw [hf]
  dsimp only
  have he : (k : ℝ) + 1 / 2 - k = 1 / 2 := by ring
  rw [he]
  simp only [lt_self_iff_false, if_false]

/-- The integer-rounding result lies between the adjacent integers. -/
theorem roundEven_bounds (x : ℝ) :
    ⌊x⌋ ≤ roundEven x ∧ roundEven x ≤ ⌊x⌋ + 1 := by
  have hm0 := Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
  have hm1 := Int.emod_lt_of_pos ⌊x⌋ (by norm_num : (0 : ℤ) < 2)
  unfold roundEven
  dsimp only
  split_ifs <;> omega

/-- Integer nearest-even rounding minimizes distance among all integers. -/
theorem roundEven_nearest (x : ℝ) (k : ℤ) :
    |(roundEven x : ℝ) - x| ≤ |(k : ℝ) - x| := by
  by_cases hk : roundEven x = k
  · rw [hk]
  have hi : (1 : ℤ) ≤ |roundEven x - k| := by
    have := abs_pos.mpr (sub_ne_zero.mpr hk)
    omega
  have hr : (1 : ℝ) ≤ |(roundEven x : ℝ) - k| := by exact_mod_cast hi
  have ht := abs_add_le ((roundEven x : ℝ) - x) (x - k)
  have he := roundEven_error x
  rw [sub_add_sub_cancel, abs_sub_comm x] at ht
  linarith

/-- Scaling preserves the nearest-point property on the integer lattice. -/
theorem scaled_roundEven_nearest (x h : ℝ) (hh : 0 < h) (k : ℤ) :
    |(roundEven (x / h) : ℝ) * h - x| ≤ |(k : ℝ) * h - x| := by
  have he := mul_le_mul_of_nonneg_right (roundEven_nearest (x / h) k) hh.le
  have hi : ∀ a : ℝ, |a - x / h| * h = |a * h - x| := by
    intro a
    rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh]
    congr 1
    field_simp
  simpa only [hi] using he

/-- Scaling gives the half-ulp absolute-error bound, including gradual underflow. -/
theorem scaled_roundEven_error (x h : ℝ) (hh : 0 < h) :
    |(roundEven (x / h) : ℝ) * h - x| ≤ h / 2 := by
  have he := mul_le_mul_of_nonneg_right (roundEven_error (x / h)) hh.le
  calc
    |(roundEven (x / h) : ℝ) * h - x| =
        |(roundEven (x / h) : ℝ) - x / h| * h := by
      rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh]
      congr 1
      field_simp
    _ ≤ h / 2 := by nlinarith [he]

end FP.IEEE
