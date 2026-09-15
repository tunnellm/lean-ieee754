import FP.IEEE.Representation
import FP.MixedError

/-! Executable rational intervals. All soundness statements concern real values. -/
namespace FP.Range

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace Interval

def Valid (I : Interval) : Prop := I.lo ≤ I.hi
instance (I : Interval) : Decidable I.Valid := inferInstanceAs (Decidable (I.lo ≤ I.hi))
def Contains (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
def zero : Interval := ⟨0, 0⟩
def radius (I : Interval) : ℚ := max |I.lo| |I.hi|
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def mul (I J : Interval) : Interval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def inflate (I : Interval) (e : ℚ) : Interval := ⟨I.lo - e, I.hi + e⟩

theorem contains_zero : zero.Contains 0 := by constructor <;> norm_num [zero]

theorem valid_of_contains {I : Interval} {x : ℝ} (hx : I.Contains x) : I.Valid := by
  exact_mod_cast hx.1.trans hx.2

theorem abs_le_radius {I : Interval} {x : ℝ} (hx : I.Contains x) : |x| ≤ (I.radius : ℝ) := by
  simp only [radius, Rat.cast_max, Rat.cast_abs]
  have hl := neg_abs_le (I.lo : ℝ)
  have hh := le_abs_self (I.hi : ℝ)
  have hml := le_max_left |(I.lo : ℝ)| |(I.hi : ℝ)|
  have hmh := le_max_right |(I.lo : ℝ)| |(I.hi : ℝ)|
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem contains_add {I J : Interval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (I.add J).Contains (x + y) := by
  simpa [Contains, add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem linear_bounds {l h x c L H : ℝ} (hx : l ≤ x ∧ x ≤ h)
    (hl : L ≤ c * l ∧ c * l ≤ H) (hh : L ≤ c * h ∧ c * h ≤ H) :
    L ≤ c * x ∧ c * x ≤ H := by
  by_cases hc : 0 ≤ c
  · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 hc, mul_le_mul_of_nonneg_left hx.2 hc]
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 hc', mul_le_mul_of_nonpos_left hx.2 hc']

theorem contains_mul {I J : Interval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (I.mul J).Contains (x * y) := by
  let L : ℝ := min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi))
    (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi))
  let H : ℝ := max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi))
    (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi))
  have hll : L ≤ (I.lo : ℝ) * J.lo ∧ (I.lo : ℝ) * J.lo ≤ H :=
    ⟨(min_le_left _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_left _ _)⟩
  have hlh : L ≤ (I.lo : ℝ) * J.hi ∧ (I.lo : ℝ) * J.hi ≤ H :=
    ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩
  have hhl : L ≤ (I.hi : ℝ) * J.lo ∧ (I.hi : ℝ) * J.lo ≤ H :=
    ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
  have hhh : L ≤ (I.hi : ℝ) * J.hi ∧ (I.hi : ℝ) * J.hi ≤ H :=
    ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hl := linear_bounds hy hll hlh
  have hh := linear_bounds hy hhl hhh
  have hv := linear_bounds hx (by simpa [mul_comm] using hl) (by simpa [mul_comm] using hh)
  simpa only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul, L, H, mul_comm] using hv

theorem contains_inflate {I : Interval} {x y : ℝ} {e : ℚ}
    (hx : I.Contains x) (he : |y - x| ≤ (e : ℝ)) : (I.inflate e).Contains y := by
  have hh := abs_le.mp he
  simp only [Contains, inflate, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hx.1, hx.2]

end Interval

/-- Exact rational parameters; the checker performs no floating-point arithmetic. -/
structure Params where
  u : ℚ
  ε : ℚ
  threshold : ℚ
  deriving Repr, DecidableEq

def Params.ofFormat (F : FP.IEEE.Format) : Params :=
  ⟨(2 : ℚ) ^ (-(F.fractionBits : ℤ) - 1),
   (2 : ℚ) ^ (F.emin - F.fractionBits) / 2,
   ((2 : ℚ) ^ (F.fractionBits + 1) - 1 / 2) * (2 : ℚ) ^ (F.emax - F.fractionBits)⟩

@[simp] theorem Params.ofFormat_u (F : FP.IEEE.Format) :
    ((Params.ofFormat F).u : ℝ) = F.unitRoundoff := by
  simp [Params.ofFormat, FP.IEEE.Format.unitRoundoff]
@[simp] theorem Params.ofFormat_ε (F : FP.IEEE.Format) :
    ((Params.ofFormat F).ε : ℝ) = F.minSubnormal / 2 := by
  simp [Params.ofFormat, FP.IEEE.Format.minSubnormal]
@[simp] theorem Params.ofFormat_threshold (F : FP.IEEE.Format) :
    ((Params.ofFormat F).threshold : ℝ) = F.overflowThreshold := by
  simp [Params.ofFormat, FP.IEEE.Format.overflowThreshold]

/-- Failure means insufficient certification, not necessarily actual overflow. -/
def checkRound (p : Params) (I : Interval) : Option Interval :=
  if I.Valid ∧ I.radius < p.threshold then some (I.inflate (p.u * I.radius + p.ε)) else none

theorem checkRound_sound (F : FP.IEEE.Format) {I J : Interval} {x : ℝ}
    (hx : I.Contains x) (hc : checkRound (.ofFormat F) I = some J) :
    |x| < F.overflowThreshold ∧ J.Contains (F.roundFinite x) := by
  unfold checkRound at hc
  split_ifs at hc with hh
  · have hJ : I.inflate ((Params.ofFormat F).u * I.radius + (Params.ofFormat F).ε) = J := Option.some.inj hc
    subst J
    have hr : (I.radius : ℝ) < F.overflowThreshold := by
      simpa using (show (I.radius : ℝ) < ((Params.ofFormat F).threshold : ℝ) by exact_mod_cast hh.2)
    refine ⟨(Interval.abs_le_radius hx).trans_lt hr, Interval.contains_inflate hx ?_⟩
    have he := F.roundFinite_mixed_error x
    have hm := mul_le_mul_of_nonneg_left (Interval.abs_le_radius hx) F.unitRoundoff_pos.le
    simp only [Rat.cast_add, Rat.cast_mul, Params.ofFormat_u, Params.ofFormat_ε]
    linarith

end FP.Range
