import FP.IEEE.Software.NearestEquivalence
import FP.IEEE.Software.NaN
import FP.IEEE.Spec.Arithmetic

/-! Executable total same-format arithmetic. All modes, operand classes,
NaN payloads, signed zeros, and operation-local flags are covered. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

def binaryExact (op : BinaryOp) (x y : ℚ) : ℚ :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y

def binaryZeroSign {I : Interchange} (op : BinaryOp) (mode : RoundingMode) (a b : Datum I) : Bool :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  if op = .mul then sa ^^ sb
  else if a.isZero && b.isZero && (sa == sb) then sa else decide (mode = .towardNegative)

def arithmeticCase (I : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a b : Datum I) : ArithmeticCase ℚ :=
  let sa := a.fields.negative
  let sb := if op = .sub then !b.fields.negative else b.fields.negative
  let zeroSign := binaryZeroSign op mode a b
  if a.isNaN || b.isNaN then .nan
  else if op = .mul then
    if (a.isZero && b.isInfinite) || (a.isInfinite && b.isZero) then .invalid
    else if a.isInfinite || b.isInfinite then .infinity (sa ^^ sb)
    else .finite (binaryExact op a.fields.rationalValue b.fields.rationalValue) zeroSign
  else if a.isInfinite && b.isInfinite && (sa != sb) then .invalid
  else if a.isInfinite then .infinity sa
  else if b.isInfinite then .infinity sb
  else .finite (binaryExact op a.fields.rationalValue b.fields.rationalValue) zeroSign

theorem binaryExact_cast (op : BinaryOp) (x y : ℚ) :
    (binaryExact op x y : ℝ) = Spec.binaryExact op (x : ℝ) (y : ℝ) := by
  cases op <;> simp [binaryExact, Spec.binaryExact]

theorem arithmeticCase_cast (I : Interchange) (op : BinaryOp) (mode : RoundingMode)
    (a b : Datum I) :
    (arithmeticCase I op mode a b).map (fun q : ℚ => (q : ℝ)) = Spec.arithmeticCase I op mode a b := by
  cases op <;> simp only [arithmeticCase, Spec.arithmeticCase, binaryZeroSign] <;>
    split_ifs <;> simp_all [ArithmeticCase.map, binaryExact_cast, Fields.rationalValue_cast, Datum.encode]

def nanResult (I : Interchange) [I.Valid] (ds : List (Datum I)) : Result I.Word :=
  let r := propagateNaN I ds
  ⟨r.value.encode, r.flags⟩

def invalidResult (I : Interchange) [I.Valid] : Result I.Word :=
  ⟨(defaultNaN I).encode, Flags.singleton .invalid⟩

def executeArithmeticCase (I : Interchange) [I.Valid] (mode : RoundingMode)
    (ds : List (Datum I)) : ArithmeticCase ℚ → Result I.Word
  | .nan => nanResult I ds
  | .invalid => invalidResult I
  | .infinity s => Result.pure (Datum.infinity s).encode
  | .finite x s => roundWithMode I mode x s

def binary (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) : Result I.Word :=
  let da := Datum.decode I a
  let db := Datum.decode I b
  executeArithmeticCase I mode [da, db] (arithmeticCase I op mode da db)

def add (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) : Result I.Word :=
  binary I .add mode a b

def sub (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) : Result I.Word :=
  binary I .sub mode a b

def mul (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) : Result I.Word :=
  binary I .mul mode a b

theorem nanResult_spec (I : Interchange) [I.Valid] (ds : List (Datum I)) :
    Spec.NaNResult I ds (nanResult I ds) := by
  constructor
  · simpa [nanResult] using propagateNaN_quiet I ds
  · exact propagateNaN_invalid I ds
  · exact propagateNaN_other_flags I ds
  · intro d h
    simpa [nanResult] using propagateNaN_selected I ds d h

theorem invalidResult_spec (I : Interchange) [I.Valid] :
    Spec.InvalidResult I (invalidResult I) := by
  constructor
  · simp [invalidResult, defaultNaN, makeQuietNaN, Datum.classify]
  · simp [invalidResult, defaultNaN, makeQuietNaN, Datum.fields]
  · simp only [invalidResult, Datum.decode_encode, defaultNaN, makeQuietNaN, Datum.fields,
      quietFraction_payload]
    simp [Interchange.payload]
  · intro e; simp [invalidResult, Flags.singleton]

theorem executeArithmeticCase_spec (I : Interchange) [I.Valid] (mode : RoundingMode)
    (ds : List (Datum I)) (c : ArithmeticCase ℚ) :
    Spec.ArithmeticResult I mode ds (c.map (fun q : ℚ => (q : ℝ)))
      (executeArithmeticCase I mode ds c) := by
  cases c with
  | nan => exact nanResult_spec I ds
  | invalid => exact invalidResult_spec I
  | infinity s => simp [Spec.ArithmeticResult, ArithmeticCase.map, executeArithmeticCase, Result.pure]
  | finite x s => exact roundWithMode_spec I mode x s

/-- Total word-and-flag refinement, with no finite-input or range hypotheses. -/
theorem binary_spec (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) : Spec.Arithmetic I op mode a b (binary I op mode a b) := by
  unfold Spec.Arithmetic binary
  rw [← arithmeticCase_cast]
  exact executeArithmeticCase_spec I mode _ _

theorem add_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) :
    Spec.Arithmetic I .add mode a b (add I mode a b) := binary_spec I .add mode a b

theorem sub_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) :
    Spec.Arithmetic I .sub mode a b (sub I mode a b) := binary_spec I .sub mode a b

theorem mul_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (a b : I.Word) :
    Spec.Arithmetic I .mul mode a b (mul I mode a b) := binary_spec I .mul mode a b

private theorem finite_datum (I : Interchange) (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) :
    d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = x := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]

/-- Finite operands use one exact rational operation and one destination rounding. -/
theorem binary_finite (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y) :
    binary I op mode a b = roundWithMode I mode (binaryExact op x y)
      (binaryZeroSign op mode (Datum.decode I a) (Datum.decode I b)) := by
  obtain ⟨han, hai, haq⟩ := finite_datum I (Datum.decode I a) x ha
  obtain ⟨hbn, hbi, hbq⟩ := finite_datum I (Datum.decode I b) y hb
  cases op <;> simp [binary, arithmeticCase, han, hai, haq, hbn, hbi, hbq, executeArithmeticCase]

/-- The existing nearest-even finite model is recovered even when the operation overflows. -/
theorem binary_even_projection (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y) :
    (Datum.decode I (binary I op .nearestEven a b).value).toRat? =
      roundNearest? I.format (binaryExact op x y) := by
  rw [binary_finite I op .nearestEven a b x y ha hb]
  exact roundWithMode_even_projection I _ _

theorem binary_even_cast (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y) :
    I.decode? (binary I op .nearestEven a b).value =
      I.format.round? (Spec.binaryExact op (x : ℝ) (y : ℝ)) := by
  rw [binary_finite I op .nearestEven a b x y ha hb, roundWithMode_even_cast, binaryExact_cast]

/-- Sharp nearest-even mixed error on actual arithmetic result words. -/
theorem binary_even_mixed_error (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (ho : overflowWithMode I.format .nearestEven (binaryExact op x y) = false) :
    ∃ z : ℝ, I.decode? (binary I op .nearestEven a b).value = some z ∧
      |z - (binaryExact op x y : ℝ)| ≤ I.format.unitRoundoff * |(binaryExact op x y : ℝ)| +
        I.format.minSubnormal / 2 := by
  rw [binary_finite I op .nearestEven a b x y ha hb]
  exact roundWithMode_even_mixed_error I _ _ ho

/-- All-mode mixed error on actual arithmetic result words. -/
theorem binary_mixed_error (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (ho : overflowWithMode I.format mode (binaryExact op x y) = false) :
    ∃ z : ℝ, I.decode? (binary I op mode a b).value = some z ∧
      |z - (binaryExact op x y : ℝ)| ≤ (2 * I.format.unitRoundoff) * |(binaryExact op x y : ℝ)| +
        I.format.minSubnormal := by
  rw [binary_finite I op mode a b x y ha hb]
  exact roundWithMode_mixed_error I mode _ _ ho

end FP.IEEE.Software
