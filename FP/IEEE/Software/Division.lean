import FP.IEEE.Software.MixedArithmetic
import FP.IEEE.Spec.Division

/-! Total exact-rational division followed by one destination rounding. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def divisionCase (A B : Interchange) (a : Datum A) (b : Datum B) : DivisionCase ℚ :=
  let sign := a.fields.negative ^^ b.fields.negative
  if a.isNaN || b.isNaN then .nan
  else if (a.isInfinite && b.isInfinite) || (a.isZero && b.isZero) then .invalid
  else if a.isInfinite then .infinity sign
  else if b.isInfinite then .zero sign
  else if b.isZero then .divideByZero sign
  else .finite (a.fields.rationalValue / b.fields.rationalValue) sign

theorem divisionCase_cast (A B : Interchange) (a : Datum A) (b : Datum B) :
    (divisionCase A B a b).map (fun q : ℚ => (q : ℝ)) = Spec.divisionCase A B a b := by
  unfold divisionCase Spec.divisionCase
  dsimp only
  split_ifs <;> simp_all [DivisionCase.map, Rat.cast_div, Fields.rationalValue_cast, Datum.encode]

def executeDivisionCase (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) : DivisionCase ℚ → Result D.Word
  | .nan => mixedNaNResult A B D a b
  | .invalid => invalidResult D
  | .infinity s => Result.pure (Datum.infinity s).encode
  | .zero s => Result.pure (Datum.zero s).encode
  | .divideByZero s => ⟨(Datum.infinity s).encode, Flags.singleton .divideByZero⟩
  | .finite x s => roundWithMode D mode x s

def mixedDiv (A B D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (b : B.Word) :
    Result D.Word := executeDivisionCase A B D mode (Datum.decode A a) (Datum.decode B b)
      (divisionCase A B (Datum.decode A a) (Datum.decode B b))

def div (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) : Result I.Word :=
  mixedDiv I I I mode a b

theorem executeDivisionCase_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : DivisionCase ℚ) :
    Spec.DivisionResult A B D mode a b (c.map (fun q : ℚ => (q : ℝ)))
      (executeDivisionCase A B D mode a b c) := by
  cases c with
  | nan => exact mixedNaNResult_spec A B D a b
  | invalid => exact invalidResult_spec D
  | infinity s => simp [Spec.DivisionResult, DivisionCase.map, executeDivisionCase, Result.pure]
  | zero s => simp [Spec.DivisionResult, DivisionCase.map, executeDivisionCase, Result.pure]
  | divideByZero s => simp [Spec.DivisionResult, DivisionCase.map, executeDivisionCase, Flags.singleton]
  | finite x s => exact roundWithMode_spec D mode x s

/-- Total result-word and five-flag refinement; no operand or range assumptions. -/
theorem mixedDiv_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (b : B.Word) :
    Spec.Division A B D mode a b (mixedDiv A B D mode a b) := by
  unfold Spec.Division mixedDiv
  rw [← divisionCase_cast]
  exact executeDivisionCase_spec A B D mode _ _ _

theorem div_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) :
    Spec.Division I I I mode a b (div I mode a b) := mixedDiv_spec I I I mode a b

private theorem finite_datum (I : Interchange) (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) : d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = x := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]

private theorem nonzero_datum (I : Interchange) (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) (hx : x ≠ 0) : d.isZero = false := by
  cases d <;> simp_all [Datum.isZero, Datum.toRat?_zero]

/-- Finite division computes the exact quotient before a single destination rounding. -/
theorem mixedDiv_finite (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hy : y ≠ 0) :
    mixedDiv A B D mode a b = roundWithMode D mode (x / y)
      ((Datum.decode A a).fields.negative ^^ (Datum.decode B b).fields.negative) := by
  obtain ⟨han, hai, haq⟩ := finite_datum A _ x ha
  obtain ⟨hbn, hbi, hbq⟩ := finite_datum B _ y hb
  have hbz := nonzero_datum B _ y hb hy
  simp [mixedDiv, divisionCase, han, hai, haq, hbn, hbi, hbq, hbz, executeDivisionCase]

theorem mixedDiv_even_projection (A B D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) (hy : y ≠ 0) :
    (Datum.decode D (mixedDiv A B D .nearestEven a b).value).toRat? = roundNearest? D.format (x / y) := by
  rw [mixedDiv_finite A B D .nearestEven a b x y ha hb hy]
  exact roundWithMode_even_projection D _ _

theorem mixedDiv_even_cast (A B D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) (hy : y ≠ 0) :
    D.decode? (mixedDiv A B D .nearestEven a b).value = D.format.round? ((x : ℝ) / (y : ℝ)) := by
  rw [mixedDiv_finite A B D .nearestEven a b x y ha hb hy, roundWithMode_even_cast, Rat.cast_div]

theorem mixedDiv_even_mixed_error (A B D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) (hy : y ≠ 0)
    (ho : overflowWithMode D.format .nearestEven (x / y) = false) :
    ∃ z : ℝ, D.decode? (mixedDiv A B D .nearestEven a b).value = some z ∧
      |z - (x / y : ℚ)| ≤ D.format.unitRoundoff * |((x / y : ℚ) : ℝ)| + D.format.minSubnormal / 2 := by
  rw [mixedDiv_finite A B D .nearestEven a b x y ha hb hy]
  exact roundWithMode_even_mixed_error D _ _ ho

theorem mixedDiv_mixed_error (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) (hy : y ≠ 0)
    (ho : overflowWithMode D.format mode (x / y) = false) :
    ∃ z : ℝ, D.decode? (mixedDiv A B D mode a b).value = some z ∧
      |z - (x / y : ℚ)| ≤ (2 * D.format.unitRoundoff) * |((x / y : ℚ) : ℝ)| + D.format.minSubnormal := by
  rw [mixedDiv_finite A B D mode a b x y ha hb hy]
  exact roundWithMode_mixed_error D mode _ _ ho

/-- The divide-by-zero flag is raised exactly for a finite nonzero dividend
and a zero divisor. Infinity divided by zero does not raise this flag. -/
theorem mixedDiv_divideByZero_iff (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) :
    (mixedDiv A B D mode a b).flags .divideByZero = true ↔
      (Datum.decode A a).isFinite = true ∧ (Datum.decode A a).isZero = false ∧
        (Datum.decode B b).isZero = true := by
  unfold mixedDiv
  generalize Datum.decode A a = da
  generalize Datum.decode B b = db
  cases da <;> cases db <;>
    simp [divisionCase, executeDivisionCase, Datum.isFinite, Datum.isZero, Datum.isInfinite,
      Datum.isNaN, mixedNaNResult, invalidResult, Result.pure, Flags.singleton, Flags.empty,
      roundWithMode, roundingFlags]

/-- Invalid is raised by a signaling NaN, zero/zero, or infinity/infinity. -/
theorem mixedDiv_invalid_iff (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) :
    (mixedDiv A B D mode a b).flags .invalid = true ↔
      (Datum.decode A a).isSignaling = true ∨ (Datum.decode B b).isSignaling = true ∨
      ((Datum.decode A a).isZero = true ∧ (Datum.decode B b).isZero = true) ∨
      ((Datum.decode A a).isInfinite = true ∧ (Datum.decode B b).isInfinite = true) := by
  unfold mixedDiv
  generalize Datum.decode A a = da
  generalize Datum.decode B b = db
  cases da <;> cases db <;>
    simp [divisionCase, executeDivisionCase, Datum.isSignaling, Datum.isZero, Datum.isInfinite,
      Datum.isNaN, mixedNaNResult, invalidResult, Result.pure, Flags.singleton, Flags.empty,
      roundWithMode, roundingFlags]

/-- Under the original Safe condition, the output is an exact quotient with a
relative perturbation of the numerator bounded by the destination unit roundoff. -/
theorem mixedDiv_even_backward (A B D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) (hy : y ≠ 0)
    (hs : D.format.Safe ((x / y : ℚ) : ℝ)) :
    ∃ z δ : ℝ, D.decode? (mixedDiv A B D .nearestEven a b).value = some z ∧
      |δ| ≤ D.format.unitRoundoff ∧ z = ((x : ℝ) * (1 + δ)) / (y : ℝ) := by
  rw [mixedDiv_finite A B D .nearestEven a b x y ha hb hy]
  obtain ⟨z, hz, δ, hδ, he⟩ := roundWithMode_even_relativeError D (x / y) _ hs
  refine ⟨z, δ, hz, hδ, ?_⟩
  rw [he, Rat.cast_div]
  ring

end FP.IEEE.Software
