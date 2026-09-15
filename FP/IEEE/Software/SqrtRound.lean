import FP.IEEE.Software.SqrtScaled

/-! Total square-root rounding, including unbounded-exponent range flags. -/
namespace FP.IEEE.Software
open Interchange

theorem sqrtRoundInt_nonneg (mode : RoundingMode) (q : ℚ) : 0 ≤ sqrtRoundInt mode q := by
  have hk : (0 : ℤ) ≤ sqrtFloor q := by positivity
  have hm : (0 : ℤ) ≤ (sqrtFloor q : ℤ) % 2 := Int.emod_nonneg _ (by norm_num)
  cases mode <;> simp only [sqrtRoundInt] <;> (try split_ifs) <;> omega

theorem sqrtAt_nonneg (mode : RoundingMode) (q : ℚ) (e : ℤ) : 0 ≤ sqrtAt mode q e := by
  unfold sqrtAt
  exact mul_nonneg (by exact_mod_cast sqrtRoundInt_nonneg mode _) (by positivity)

def sqrtOverflow (F : Format) (mode : RoundingMode) (q : ℚ) : Bool :=
  decide (maxFinite F < |sqrtPrecision F mode q|)

def sqrtTiny (F : Format) (mode : RoundingMode) (q : ℚ) : Bool :=
  decide (0 < |sqrtPrecision F mode q| ∧ |sqrtPrecision F mode q| < (2 : ℚ)^F.emin)

def sqrtInexact (F : Format) (mode : RoundingMode) (q : ℚ) : Bool :=
  decide ((sqrtScaled F mode q)^2 ≠ q)

theorem sqrtOverflow_spec (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    sqrtOverflow F mode q = true ↔ Spec.OverflowWithMode F mode (Real.sqrt (q : ℝ)) := by
  simp only [sqrtOverflow, decide_eq_true_eq, Spec.OverflowWithMode]
  rw [← sqrtPrecision_cast F mode q hq, ← maxFinite_cast]
  exact (by exact_mod_cast (Iff.rfl : maxFinite F < |sqrtPrecision F mode q| ↔ _))

theorem sqrtTiny_spec (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    sqrtTiny F mode q = true ↔ Spec.TinyWithMode F mode (Real.sqrt (q : ℝ)) := by
  simp only [sqrtTiny, decide_eq_true_eq, Spec.TinyWithMode, Format.minNormal]
  rw [← sqrtPrecision_cast F mode q hq]
  have he : (((2 : ℚ)^F.emin : ℚ) : ℝ) = (2 : ℝ)^F.emin := by push_cast; rfl
  rw [← he]
  norm_cast

theorem sqrtInexact_spec (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    sqrtInexact F mode q = true ↔ Spec.roundWithMode F mode (Real.sqrt (q : ℝ)) ≠ Real.sqrt (q : ℝ) := by
  simp only [sqrtInexact, decide_eq_true_eq]
  rw [← sqrtScaled_cast F mode q hq]
  apply not_congr
  have hn : (0 : ℝ) ≤ (sqrtScaled F mode q : ℝ) := by
    exact_mod_cast sqrtAt_nonneg mode q _
  have hs := Real.sq_sqrt (show 0 ≤ (q : ℝ) by exact_mod_cast hq)
  have hp := Real.sqrt_nonneg (q : ℝ)
  have hc : (sqrtScaled F mode q)^2 = q ↔ ((sqrtScaled F mode q : ℚ) : ℝ)^2 = (q : ℝ) := by norm_cast
  rw [hc]
  constructor <;> intro h <;> nlinarith

def sqrtFlags (F : Format) (mode : RoundingMode) (q : ℚ) : Flags
  | .invalid | .divideByZero => false
  | .overflow => sqrtOverflow F mode q
  | .inexact => sqrtOverflow F mode q || sqrtInexact F mode q
  | .underflow => !sqrtOverflow F mode q && sqrtInexact F mode q && sqrtTiny F mode q

theorem sqrtFlags_spec (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    Spec.RoundingFlags F mode (Real.sqrt (q : ℝ)) (sqrtFlags F mode q) := by
  constructor
  · rfl
  · rfl
  · exact sqrtOverflow_spec F mode q hq
  · simp [sqrtFlags, sqrtOverflow_spec F mode q hq, sqrtInexact_spec F mode q hq]
  · simp [sqrtFlags, Bool.eq_false_iff, sqrtOverflow_spec F mode q hq,
      sqrtInexact_spec F mode q hq, sqrtTiny_spec F mode q hq, and_assoc]

theorem sqrtScaled_representable (F : Format) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q)
    (ho : sqrtOverflow F mode q = false) : F.Representable (sqrtScaled F mode q : ℝ) := by
  rw [sqrtScaled_cast F mode q hq]
  apply Spec.roundWithMode_representable
  simpa [← sqrtOverflow_spec F mode q hq] using ho

/-- Exact rational implementation for a nonnegative radicand. The proof argument
is erased; computation uses only integer square root and rational comparisons. -/
def roundSqrt (I : Interchange) (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) : Result I.Word :=
  ⟨if ho : sqrtOverflow I.format mode q = true then (overflowResult I mode false).value
    else encodeFinite I (sqrtScaled I.format mode q) false
      (sqrtScaled_representable I.format mode q hq (Bool.eq_false_iff.mpr ho)),
    sqrtFlags I.format mode q⟩

private theorem sqrt_sign (q : ℚ) : Spec.realSign (Real.sqrt (q : ℝ)) false = false := by
  simp [Spec.realSign, not_lt.mpr (Real.sqrt_nonneg (q : ℝ))]

/-- Full real square-root rounding contract, without range assumptions. -/
theorem roundSqrt_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (q : ℚ) (hq : 0 ≤ q) :
    Spec.Rounding I mode (Real.sqrt (q : ℝ)) false (roundSqrt I mode q hq) := by
  classical
  have hc := sqrtOverflow_spec I.format mode q hq
  by_cases ho : sqrtOverflow I.format mode q = true
  · have hs := overflowResult_spec I mode false
    have hr := hc.mp ho
    constructor
    · intro h; exact (h hr).elim
    · intro _ h
      simpa [roundSqrt, ho, sqrt_sign] using hs.1 (by simpa [sqrt_sign] using h)
    · intro _ h
      simpa [roundSqrt, ho, sqrt_sign] using hs.2.1 (by simpa [sqrt_sign] using h)
    · simpa [roundSqrt, ho, hr, sqrt_sign] using hs.2.2.1
    · exact sqrtFlags_spec I.format mode q hq
  · have hn := Bool.eq_false_iff.mpr ho
    have hr : ¬ Spec.OverflowWithMode I.format mode (Real.sqrt (q : ℝ)) := fun h => ho (hc.mpr h)
    have hv := encodeFinite_spec I (sqrtScaled I.format mode q) false
      (sqrtScaled_representable I.format mode q hq hn)
    constructor
    · intro _
      simpa [roundSqrt, ho, sqrtScaled_cast I.format mode q hq] using hv.1
    · intro h; exact (hr h).elim
    · intro h; exact (hr h).elim
    · simpa [roundSqrt, ho, hr, valueSign_cast, sqrtScaled_cast I.format mode q hq, sqrt_sign] using hv.2
    · exact sqrtFlags_spec I.format mode q hq
end FP.IEEE.Software
