import FP.IEEE.Software.SqrtRound
import FP.IEEE.Software.Conversion
import FP.IEEE.Spec.Sqrt

/-! Total square root with independently specified real-value and flag semantics. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def mixedSqrt (A D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) : Result D.Word :=
  let d := Datum.decode A a
  if d.isNaN then
    ⟨convertNaN A D d, fun e => if e = .invalid then d.isSignaling else false⟩
  else if d.isZero then Result.pure (Datum.zero d.fields.negative).encode
  else if d.isInfinite then
    if d.fields.negative then invalidResult D else Result.pure (Datum.infinity false).encode
  else if h : d.fields.rationalValue < 0 then invalidResult D
  else roundSqrt D mode d.fields.rationalValue (le_of_not_gt h)

def sqrt (I : Interchange) [I.Valid] (mode : RoundingMode) (a : I.Word) : Result I.Word :=
  mixedSqrt I I mode a

theorem mixedSqrt_spec (A D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) :
    Spec.Sqrt A D mode a (mixedSqrt A D mode a) := by
  have hv : (((Datum.decode A a).fields.rationalValue : ℚ) : ℝ) = A.value a := by
    rw [Fields.rationalValue_cast]
    change A.value (Datum.decode A a).encode = A.value a
    rw [Datum.encode_decode]
  have hn : (Datum.decode A a).fields.rationalValue < 0 ↔ A.value a < 0 := by
    rw [← hv]; exact_mod_cast (Iff.rfl : (Datum.decode A a).fields.rationalValue < 0 ↔ _)
  unfold Spec.Sqrt mixedSqrt
  dsimp only
  simp only [← hn]
  split_ifs with hnan hz hi hs hneg
  · exact ⟨convertNaN_spec A D _, by simp, fun e he => by simp [he]⟩
  · simp [Result.pure]
  · exact invalidResult_spec D
  · simp [Result.pure]
  · exact invalidResult_spec D
  · have hr := roundSqrt_spec D mode (Datum.decode A a).fields.rationalValue
      (le_of_not_gt hneg)
    simpa only [hv] using hr

theorem sqrt_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a : I.Word) :
    Spec.Sqrt I I mode a (sqrt I mode a) := mixedSqrt_spec I I mode a

private theorem finite_positive_datum (A : Interchange) (d : Datum A) (q : ℚ)
    (ha : d.toRat? = some q) (hq : 0 < q) :
    d.isNaN = false ∧ d.isInfinite = false ∧ d.isZero = false ∧ d.fields.rationalValue = q := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite,
    Datum.isZero, Fields.rationalValue]

/-- Positive finite operands reach the exact square-root rounder without source conversion. -/
theorem mixedSqrt_positive (A D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (q : ℚ) (ha : (Datum.decode A a).toRat? = some q) (hq : 0 < q) :
    mixedSqrt A D mode a = roundSqrt D mode q hq.le := by
  obtain ⟨hn, hi, hz, hv⟩ := finite_positive_datum A _ q ha hq
  simp only [mixedSqrt, hn, hi, hz, Bool.false_eq_true, if_false]
  simp [hv, not_lt.mpr hq.le]

theorem mixedSqrt_mixed_error (A D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (q : ℚ) (ha : (Datum.decode A a).toRat? = some q) (hq : 0 < q)
    (ho : sqrtOverflow D.format mode q = false) :
    ∃ r : ℝ, D.decode? (mixedSqrt A D mode a).value = some r ∧
      |r - Real.sqrt (q : ℝ)| ≤ (2 * D.format.unitRoundoff) * |Real.sqrt (q : ℝ)| + D.format.minSubnormal := by
  rw [mixedSqrt_positive A D mode a q ha hq]
  refine ⟨Spec.roundWithMode D.format mode (Real.sqrt (q : ℝ)), ?_,
    Spec.roundWithMode_mixed_error D.format mode _⟩
  exact (roundSqrt_spec D mode q hq.le).finite (by simpa [← sqrtOverflow_spec D.format mode q hq.le] using ho)

theorem mixedSqrt_even_mixed_error (A D : Interchange) [D.Valid]
    (a : A.Word) (q : ℚ) (ha : (Datum.decode A a).toRat? = some q) (hq : 0 < q)
    (ho : sqrtOverflow D.format .nearestEven q = false) :
    ∃ r : ℝ, D.decode? (mixedSqrt A D .nearestEven a).value = some r ∧
      |r - Real.sqrt (q : ℝ)| ≤ D.format.unitRoundoff * |Real.sqrt (q : ℝ)| + D.format.minSubnormal / 2 := by
  rw [mixedSqrt_positive A D .nearestEven a q ha hq]
  refine ⟨D.format.roundFinite (Real.sqrt (q : ℝ)), ?_, D.format.roundFinite_mixed_error _⟩
  exact (roundSqrt_spec D .nearestEven q hq.le).finite
    (by simpa [← sqrtOverflow_spec D.format .nearestEven q hq.le] using ho)

/-- Relative perturbation of the square-root result, derived from rounding. -/
theorem mixedSqrt_even_relativeError (A D : Interchange) [D.Valid]
    (a : A.Word) (q : ℚ) (ha : (Datum.decode A a).toRat? = some q) (hq : 0 < q)
    (ho : sqrtOverflow D.format .nearestEven q = false)
    (hs : D.format.Safe (Real.sqrt (q : ℝ))) :
    ∃ r : ℝ, D.decode? (mixedSqrt A D .nearestEven a).value = some r ∧
      FP.RelativeError D.format.unitRoundoff (Real.sqrt (q : ℝ)) r := by
  rw [mixedSqrt_positive A D .nearestEven a q ha hq]
  exact ⟨_, (roundSqrt_spec D .nearestEven q hq.le).finite
    (by simpa [← sqrtOverflow_spec D.format .nearestEven q hq.le] using ho),
    D.format.roundFinite_relativeError hs⟩

/-- Square root preserves either zero sign, without raising an exception. -/
theorem mixedSqrt_zero (A D : Interchange) [A.Valid] [D.Valid] (mode : RoundingMode) (s : Bool) :
    mixedSqrt A D mode (Datum.zero s).encode = Result.pure (Datum.zero s).encode := by
  simp [mixedSqrt, Datum.isNaN, Datum.isZero, Datum.fields]

/-- Backward stability with respect to the radicand. -/
theorem mixedSqrt_even_backward (A D : Interchange) [D.Valid]
    (a : A.Word) (q : ℚ) (ha : (Datum.decode A a).toRat? = some q) (hq : 0 < q)
    (ho : sqrtOverflow D.format .nearestEven q = false)
    (hs : D.format.Safe (Real.sqrt (q : ℝ))) :
    ∃ r θ : ℝ, D.decode? (mixedSqrt A D .nearestEven a).value = some r ∧
      |θ| ≤ 2 * D.format.unitRoundoff + D.format.unitRoundoff^2 ∧
      r = Real.sqrt ((q : ℝ) * (1 + θ)) := by
  obtain ⟨r, hr, δ, hd, he⟩ := mixedSqrt_even_relativeError A D a q ha hq ho hs
  have hfinite := (roundSqrt_spec D .nearestEven q hq.le).finite
    (by simpa [← sqrtOverflow_spec D.format .nearestEven q hq.le] using ho)
  rw [← mixedSqrt_positive A D .nearestEven a q ha hq, hr] at hfinite
  have heq : r = (sqrtScaled D.format .nearestEven q : ℝ) := by
    simpa [sqrtScaled_cast D.format .nearestEven q hq.le] using Option.some.inj hfinite
  have hrn : 0 ≤ r := by
    rw [heq]
    exact_mod_cast sqrtAt_nonneg .nearestEven q _
  have hd2 : δ^2 ≤ D.format.unitRoundoff^2 := by
    nlinarith [sq_abs δ, mul_self_le_mul_self (abs_nonneg δ) hd]
  have hb : |2*δ + δ^2| ≤ 2*D.format.unitRoundoff + D.format.unitRoundoff^2 := by
    have ht := abs_add_le (2*δ) (δ^2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg δ)] at ht
    norm_num at ht
    linarith
  refine ⟨r, 2*δ + δ^2, hr, hb, ?_⟩
  have hsq : r^2 = (q : ℝ) * (1 + (2*δ + δ^2)) := by
    rw [he, mul_pow, Real.sq_sqrt (show 0 ≤ (q : ℝ) by exact_mod_cast hq.le)]
    ring
  rw [← hsq, Real.sqrt_sq hrn]
end FP.IEEE.Software
