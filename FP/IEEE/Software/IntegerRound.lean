import FP.IEEE.Environment
import FP.IEEE.Rounding

/-! Executable rounding of exact rational numbers to the integer lattice.
The correctness statements quantify over every integer candidate. This is the
quotient/remainder-independent foundation for rounding scaled significands. -/
namespace FP.IEEE.Software

/-- An integer minimizing distance to the exact rational input. -/
def NearestInt (x : ℚ) (n : ℤ) : Prop :=
  ∀ k : ℤ, |(n : ℚ) - x| ≤ |(k : ℚ) - x|

/-- Executable rounding; the tie test uses exact rational comparison. -/
def roundInt (mode : RoundingMode) (x : ℚ) : ℤ :=
  match mode with
  | .towardNegative => ⌊x⌋
  | .towardPositive => ⌈x⌉
  | .towardZero => if x < 0 then ⌈x⌉ else ⌊x⌋
  | .nearestEven =>
    let k := ⌊x⌋
    if x - k < 1 / 2 then k
    else if 1 / 2 < x - k then k + 1
    else k + k % 2
  | .nearestAway =>
    let k := ⌊x⌋
    if x - k < 1 / 2 then k
    else if 1 / 2 < x - k then k + 1
    else if x < 0 then k else k + 1

@[simp] theorem roundInt_intCast (mode : RoundingMode) (k : ℤ) :
    roundInt mode (k : ℚ) = k := by
  cases mode <;> simp [roundInt]

@[simp] theorem roundInt_zero (mode : RoundingMode) : roundInt mode 0 = 0 := by
  simpa using roundInt_intCast mode 0

/-- Greatest integer below the input, stated without reference to the algorithm. -/
theorem roundInt_down (x : ℚ) :
    (roundInt .towardNegative x : ℚ) ≤ x ∧
      ∀ k : ℤ, (k : ℚ) ≤ x → k ≤ roundInt .towardNegative x := by
  exact ⟨Int.floor_le x, fun _ h => Int.le_floor.mpr h⟩

/-- Least integer above the input. -/
theorem roundInt_up (x : ℚ) :
    x ≤ (roundInt .towardPositive x : ℚ) ∧
      ∀ k : ℤ, x ≤ (k : ℚ) → roundInt .towardPositive x ≤ k := by
  exact ⟨Int.le_ceil x, fun _ h => Int.ceil_le.mpr h⟩

theorem roundInt_zero_direction (x : ℚ) :
    (x < 0 → roundInt .towardZero x = roundInt .towardPositive x) ∧
    (0 ≤ x → roundInt .towardZero x = roundInt .towardNegative x) := by
  constructor <;> intro h <;> simp [roundInt, h, not_lt.mpr]

theorem roundInt_nearest_error (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : ℚ) :
    |(roundInt mode x : ℚ) - x| ≤ 1 / 2 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  have hm0 : (0 : ℚ) ≤ (⌊x⌋ % 2 : ℤ) := by
    exact_mod_cast Int.emod_nonneg ⌊x⌋ (by norm_num : (2 : ℤ) ≠ 0)
  have hm1 : ((⌊x⌋ % 2 : ℤ) : ℚ) ≤ 1 := by
    exact_mod_cast (show ⌊x⌋ % 2 ≤ 1 by omega)
  rcases hm with rfl | rfl <;> unfold roundInt <;> dsimp only <;>
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- Half a lattice spacing suffices to establish global nearest-point optimality. -/
theorem nearestInt_of_error (x : ℚ) (n : ℤ) (h : |(n : ℚ) - x| ≤ 1 / 2) :
    NearestInt x n := by
  intro k
  by_cases hk : n = k
  · rw [hk]
  have hi : (1 : ℤ) ≤ |n - k| := by
    have := abs_pos.mpr (sub_ne_zero.mpr hk)
    omega
  have hr : (1 : ℚ) ≤ |(n : ℚ) - k| := by exact_mod_cast hi
  have ht := abs_add_le ((n : ℚ) - x) (x - k)
  rw [sub_add_sub_cancel, abs_sub_comm x] at ht
  linarith

theorem roundInt_nearest (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : ℚ) :
    NearestInt x (roundInt mode x) :=
  nearestInt_of_error x _ (roundInt_nearest_error mode hm x)

theorem roundInt_even_midpoint (k : ℤ) :
    roundInt .nearestEven ((k : ℚ) + 1 / 2) = k + k % 2 := by
  have hf : ⌊(k : ℚ) + 1 / 2⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  simp only [roundInt, hf]
  norm_num

/-- The selected midpoint result is even, including for negative inputs. -/
theorem roundInt_even_midpoint_even (k : ℤ) :
    roundInt .nearestEven ((k : ℚ) + 1 / 2) % 2 = 0 := by
  rw [roundInt_even_midpoint]
  omega

theorem roundInt_away_midpoint (k : ℤ) :
    roundInt .nearestAway ((k : ℚ) + 1 / 2) = if k < 0 then k else k + 1 := by
  have hf : ⌊(k : ℚ) + 1 / 2⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  have hs : (k : ℚ) + 1 / 2 < 0 ↔ k < 0 := by
    constructor
    · intro h; exact_mod_cast (show (k : ℚ) < 0 by linarith)
    · intro h
      have : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      linarith
  simp only [roundInt, hf]
  have he : (k : ℚ) + 1 / 2 - k = 1 / 2 := by ring
  rw [he]
  simp only [lt_self_iff_false, if_false, hs]

/-- Compatibility with the existing real nearest-even integer specification. -/
theorem roundInt_even_equiv (x : ℚ) :
    roundInt .nearestEven x = FP.IEEE.roundEven (x : ℝ) := by
  have hf : ⌊(x : ℝ)⌋ = ⌊x⌋ := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast Int.floor_le x
    · exact_mod_cast Int.lt_floor_add_one x
  have hl : (x : ℝ) - (⌊x⌋ : ℤ) < 1 / 2 ↔ x - (⌊x⌋ : ℚ) < 1 / 2 := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := x - (⌊x⌋ : ℚ)) (q := 1 / 2))
  have hh : (1 : ℝ) / 2 < (x : ℝ) - (⌊x⌋ : ℤ) ↔ 1 / 2 < x - (⌊x⌋ : ℚ) := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := 1 / 2) (q := x - (⌊x⌋ : ℚ)))
  simp only [roundInt, FP.IEEE.roundEven, hf, hl, hh]

end FP.IEEE.Software
