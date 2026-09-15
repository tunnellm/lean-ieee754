import FP.IEEE.Software.MixedArithmetic
import FP.IEEE.Spec.FMA

/-! Executable FMA with heterogeneous sources and one destination rounding. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def fmaNaNResult (A B C D : Interchange) [D.Valid]
    (a : Datum A) (b : Datum B) (c : Datum C) : Result D.Word :=
  ⟨if a.isSignaling then convertNaN A D a
   else if b.isSignaling then convertNaN B D b
   else if c.isSignaling then convertNaN C D c
   else if a.isNaN then convertNaN A D a
   else if b.isNaN then convertNaN B D b
   else convertNaN C D c,
   fun e => if e = .invalid then
     a.isSignaling || b.isSignaling || c.isSignaling || Spec.invalidProduct a b else false⟩

theorem fmaNaNResult_spec (A B C D : Interchange) [D.Valid]
    (a : Datum A) (b : Datum B) (c : Datum C) :
    Spec.FmaNaN A B C D a b c (fmaNaNResult A B C D a b c) := by
  unfold Spec.FmaNaN fmaNaNResult
  refine ⟨?_, by simp, ?_⟩
  · split_ifs <;> apply convertNaN_spec
  · intro e he
    simp [he]

def fmaCase (A B C : Interchange) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) : ArithmeticCase ℚ :=
  let s := a.fields.negative ^^ b.fields.negative
  if a.isNaN || b.isNaN || c.isNaN then .nan
  else if Spec.invalidProduct a b then .invalid
  else if (a.isInfinite || b.isInfinite) && c.isInfinite && (s != c.fields.negative) then .invalid
  else if a.isInfinite || b.isInfinite then .infinity s
  else if c.isInfinite then .infinity c.fields.negative
  else .finite (a.fields.rationalValue * b.fields.rationalValue + c.fields.rationalValue)
    (Spec.fmaZeroSign mode a b c)

theorem fmaCase_cast (A B C : Interchange) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) :
    (fmaCase A B C mode a b c).map (fun q : ℚ => (q : ℝ)) = Spec.fmaCase A B C mode a b c := by
  unfold fmaCase Spec.fmaCase
  dsimp only
  split_ifs <;> simp_all [ArithmeticCase.map, Rat.cast_add, Rat.cast_mul,
    Fields.rationalValue_cast, Datum.encode]

def executeFmaCase (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) : ArithmeticCase ℚ → Result D.Word
  | .nan => fmaNaNResult A B C D a b c
  | .invalid => invalidResult D
  | .infinity s => Result.pure (Datum.infinity s).encode
  | .finite x s => roundWithMode D mode x s

def mixedFma (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (c : C.Word) : Result D.Word :=
  executeFmaCase A B C D mode (Datum.decode A a) (Datum.decode B b) (Datum.decode C c)
    (fmaCase A B C mode (Datum.decode A a) (Datum.decode B b) (Datum.decode C c))

def fma (I : Interchange) [I.Valid] (mode : RoundingMode) (a b c : I.Word) : Result I.Word :=
  mixedFma I I I I mode a b c

theorem executeFmaCase_spec (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : Datum C) (k : ArithmeticCase ℚ) :
    Spec.FmaResult A B C D mode a b c (k.map (fun q : ℚ => (q : ℝ)))
      (executeFmaCase A B C D mode a b c k) := by
  cases k with
  | nan => exact fmaNaNResult_spec A B C D a b c
  | invalid => exact invalidResult_spec D
  | infinity s => simp [Spec.FmaResult, ArithmeticCase.map, executeFmaCase, Result.pure]
  | finite x s => exact roundWithMode_spec D mode x s

/-- Total refinement of both the result word and all five flags. -/
theorem mixedFma_spec (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (c : C.Word) :
    Spec.Fma A B C D mode a b c (mixedFma A B C D mode a b c) := by
  unfold Spec.Fma mixedFma
  rw [← fmaCase_cast]
  exact executeFmaCase_spec A B C D mode _ _ _ _

theorem fma_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b c : I.Word) :
    Spec.Fma I I I I mode a b c (fma I mode a b c) := mixedFma_spec I I I I mode a b c

private theorem finite_datum (I : Interchange) (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) : d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = x := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]

theorem mixedFma_finite (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (c : C.Word) (x y z : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hc : (Datum.decode C c).toRat? = some z) :
    mixedFma A B C D mode a b c = roundWithMode D mode (x * y + z)
      (Spec.fmaZeroSign mode (Datum.decode A a) (Datum.decode B b) (Datum.decode C c)) := by
  obtain ⟨han, hai, haq⟩ := finite_datum A _ x ha
  obtain ⟨hbn, hbi, hbq⟩ := finite_datum B _ y hb
  obtain ⟨hcn, hci, hcq⟩ := finite_datum C _ z hc
  simp [mixedFma, fmaCase, Spec.invalidProduct, han, hai, haq, hbn, hbi, hbq,
    hcn, hci, hcq, executeFmaCase]

theorem mixedFma_even_cast (A B C D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (c : C.Word) (x y z : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hc : (Datum.decode C c).toRat? = some z) :
    D.decode? (mixedFma A B C D .nearestEven a b c).value =
      D.format.round? ((x : ℝ) * (y : ℝ) + (z : ℝ)) := by
  rw [mixedFma_finite A B C D .nearestEven a b c x y z ha hb hc,
    roundWithMode_even_cast, Rat.cast_add, Rat.cast_mul]

theorem mixedFma_even_mixed_error (A B C D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (c : C.Word) (x y z : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hc : (Datum.decode C c).toRat? = some z)
    (ho : overflowWithMode D.format .nearestEven (x * y + z) = false) :
    ∃ r : ℝ, D.decode? (mixedFma A B C D .nearestEven a b c).value = some r ∧
      |r - (x * y + z : ℚ)| ≤ D.format.unitRoundoff * |((x * y + z : ℚ) : ℝ)| +
        D.format.minSubnormal / 2 := by
  rw [mixedFma_finite A B C D .nearestEven a b c x y z ha hb hc]
  exact roundWithMode_even_mixed_error D _ _ ho

theorem mixedFma_mixed_error (A B C D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (c : C.Word) (x y z : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hc : (Datum.decode C c).toRat? = some z)
    (ho : overflowWithMode D.format mode (x * y + z) = false) :
    ∃ r : ℝ, D.decode? (mixedFma A B C D mode a b c).value = some r ∧
      |r - (x * y + z : ℚ)| ≤ (2 * D.format.unitRoundoff) * |((x * y + z : ℚ) : ℝ)| +
        D.format.minSubnormal := by
  rw [mixedFma_finite A B C D mode a b c x y z ha hb hc]
  exact roundWithMode_mixed_error D mode _ _ ho

/-- One relative perturbation suffices for both the multiplicand and addend.
The qualification is on the exact fused result, so cancellation is permitted. -/
theorem mixedFma_even_backward (A B C D : Interchange) [D.Valid]
    (a : A.Word) (b : B.Word) (c : C.Word) (x y z : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (hc : (Datum.decode C c).toRat? = some z)
    (hs : D.format.Safe ((x * y + z : ℚ) : ℝ)) :
    ∃ r δ : ℝ, D.decode? (mixedFma A B C D .nearestEven a b c).value = some r ∧
      |δ| ≤ D.format.unitRoundoff ∧
      r = ((x : ℝ) * (1 + δ)) * (y : ℝ) + (z : ℝ) * (1 + δ) := by
  rw [mixedFma_finite A B C D .nearestEven a b c x y z ha hb hc]
  obtain ⟨r, hr, δ, hd, he⟩ := roundWithMode_even_relativeError D (x * y + z) _ hs
  refine ⟨r, δ, hr, hd, ?_⟩
  rw [he, Rat.cast_add, Rat.cast_mul]
  ring
end FP.IEEE.Software
