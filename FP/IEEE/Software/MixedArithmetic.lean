import FP.IEEE.Software.Conversion
import FP.IEEE.Spec.MixedArithmetic

/-! Mixed-precision arithmetic without premature operand rounding. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def mixedZeroSign {A B : Interchange} (op : BinaryOp) (mode : RoundingMode) (a : Datum A) (b : Datum B) : Bool :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  if op = .mul then sa ^^ sb
  else if a.isZero && b.isZero && (sa == sb) then sa else decide (mode = .towardNegative)

def mixedCase (A B : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) : ArithmeticCase ℚ :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  let zeroSign := mixedZeroSign op mode a b
  if a.isNaN || b.isNaN then .nan
  else if op = .mul then
    if (a.isZero && b.isInfinite) || (a.isInfinite && b.isZero) then .invalid
    else if a.isInfinite || b.isInfinite then .infinity (sa ^^ sb)
    else .finite (binaryExact op a.fields.rationalValue b.fields.rationalValue) zeroSign
  else if a.isInfinite && b.isInfinite && (sa != sb) then .invalid
  else if a.isInfinite then .infinity sa
  else if b.isInfinite then .infinity sb
  else .finite (binaryExact op a.fields.rationalValue b.fields.rationalValue) zeroSign

theorem mixedCase_cast (A B : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a : Datum A) (b : Datum B) :
    (mixedCase A B op mode a b).map (fun q : ℚ => (q : ℝ)) = Spec.mixedCase A B op mode a b := by
  cases op <;> simp only [mixedCase, Spec.mixedCase, mixedZeroSign] <;>
    split_ifs <;> simp_all [ArithmeticCase.map, binaryExact_cast, Fields.rationalValue_cast, Datum.encode]

def chooseLeftNaN {A B : Interchange} (a : Datum A) (b : Datum B) : Bool :=
  a.isSignaling || (!b.isSignaling && a.isNaN)

def mixedNaNResult (A B D : Interchange) [D.Valid] (a : Datum A) (b : Datum B) : Result D.Word :=
  ⟨if chooseLeftNaN a b then convertNaN A D a else convertNaN B D b,
    fun e => (e == .invalid) && (a.isSignaling || b.isSignaling)⟩

def executeMixedCase (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) : ArithmeticCase ℚ → Result D.Word
  | .nan => mixedNaNResult A B D a b
  | .invalid => invalidResult D
  | .infinity s => Result.pure (Datum.infinity s).encode
  | .finite x s => roundWithMode D mode x s

def mixedBinary (A B D : Interchange) [D.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) : Result D.Word :=
  executeMixedCase A B D mode (Datum.decode A a) (Datum.decode B b)
    (mixedCase A B op mode (Datum.decode A a) (Datum.decode B b))

def mixedAdd (A B D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (b : B.Word) :
    Result D.Word := mixedBinary A B D .add mode a b

def mixedSub (A B D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (b : B.Word) :
    Result D.Word := mixedBinary A B D .sub mode a b

def mixedMul (A B D : Interchange) [D.Valid] (mode : RoundingMode) (a : A.Word) (b : B.Word) :
    Result D.Word := mixedBinary A B D .mul mode a b

theorem mixedNaNResult_spec (A B D : Interchange) [D.Valid] (a : Datum A) (b : Datum B) :
    Spec.MixedNaN A B D a b (mixedNaNResult A B D a b) := by
  unfold Spec.MixedNaN mixedNaNResult
  change (if chooseLeftNaN a b then _ else _) ∧ _
  refine ⟨?_, by simp, ?_⟩
  · split_ifs
    · exact convertNaN_spec A D a
    · exact convertNaN_spec B D b
  · intro e he; simp [he]

theorem executeMixedCase_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : Datum A) (b : Datum B) (c : ArithmeticCase ℚ) :
    Spec.MixedArithmeticResult A B D mode a b (c.map (fun q : ℚ => (q : ℝ)))
      (executeMixedCase A B D mode a b c) := by
  cases c with
  | nan => exact mixedNaNResult_spec A B D a b
  | invalid => exact invalidResult_spec D
  | infinity s => simp [Spec.MixedArithmeticResult, ArithmeticCase.map, executeMixedCase, Result.pure]
  | finite x s => exact roundWithMode_spec D mode x s

theorem mixedBinary_spec (A B D : Interchange) [D.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) : Spec.MixedArithmetic A B D op mode a b (mixedBinary A B D op mode a b) := by
  unfold Spec.MixedArithmetic mixedBinary
  rw [← mixedCase_cast]
  exact executeMixedCase_spec A B D mode _ _ _

private theorem finite_datum (I : Interchange) (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) :
    d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = x := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]

/-- No source-to-destination conversion occurs before the exact operation. -/
theorem mixedBinary_finite (A B D : Interchange) [D.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) :
    mixedBinary A B D op mode a b = roundWithMode D mode (binaryExact op x y)
      (mixedZeroSign op mode (Datum.decode A a) (Datum.decode B b)) := by
  obtain ⟨han, hai, haq⟩ := finite_datum A (Datum.decode A a) x ha
  obtain ⟨hbn, hbi, hbq⟩ := finite_datum B (Datum.decode B b) y hb
  cases op <;> simp [mixedBinary, mixedCase, han, hai, haq, hbn, hbi, hbq, executeMixedCase]

theorem mixedBinary_even_projection (A B D : Interchange) [D.Valid] (op : BinaryOp)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y) :
    (Datum.decode D (mixedBinary A B D op .nearestEven a b).value).toRat? =
      roundNearest? D.format (binaryExact op x y) := by
  rw [mixedBinary_finite A B D op .nearestEven a b x y ha hb]
  exact roundWithMode_even_projection D _ _

theorem mixedBinary_even_mixed_error (A B D : Interchange) [D.Valid] (op : BinaryOp)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (ho : overflowWithMode D.format .nearestEven (binaryExact op x y) = false) :
    ∃ z : ℝ, D.decode? (mixedBinary A B D op .nearestEven a b).value = some z ∧
      |z - (binaryExact op x y : ℝ)| ≤ D.format.unitRoundoff * |(binaryExact op x y : ℝ)| +
        D.format.minSubnormal / 2 := by
  rw [mixedBinary_finite A B D op .nearestEven a b x y ha hb]
  exact roundWithMode_even_mixed_error D _ _ ho

theorem mixedAdd_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) : Spec.MixedArithmetic A B D .add mode a b (mixedAdd A B D mode a b) :=
  mixedBinary_spec A B D .add mode a b

theorem mixedSub_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) : Spec.MixedArithmetic A B D .sub mode a b (mixedSub A B D mode a b) :=
  mixedBinary_spec A B D .sub mode a b

theorem mixedMul_spec (A B D : Interchange) [D.Valid] (mode : RoundingMode)
    (a : A.Word) (b : B.Word) : Spec.MixedArithmetic A B D .mul mode a b (mixedMul A B D mode a b) :=
  mixedBinary_spec A B D .mul mode a b

theorem mixedBinary_mixed_error (A B D : Interchange) [D.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a : A.Word) (b : B.Word) (x y : ℚ)
    (ha : (Datum.decode A a).toRat? = some x) (hb : (Datum.decode B b).toRat? = some y)
    (ho : overflowWithMode D.format mode (binaryExact op x y) = false) :
    ∃ z : ℝ, D.decode? (mixedBinary A B D op mode a b).value = some z ∧
      |z - (binaryExact op x y : ℝ)| ≤ (2 * D.format.unitRoundoff) * |(binaryExact op x y : ℝ)| +
        D.format.minSubnormal := by
  rw [mixedBinary_finite A B D op mode a b x y ha hb]
  exact roundWithMode_mixed_error D mode _ _ ho

theorem mixedBinary_same_finite (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y) :
    mixedBinary I I I op mode a b = binary I op mode a b := by
  rw [mixedBinary_finite I I I op mode a b x y ha hb, binary_finite I op mode a b x y ha hb]
  rfl

end FP.IEEE.Software
