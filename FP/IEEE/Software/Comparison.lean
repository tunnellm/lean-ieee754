import FP.IEEE.Projection
import FP.IEEE.Environment

/-! Classification and comparison over all raw encodings. NaNs are unordered,
zero signs compare equal, and exception behavior is explicit. -/
namespace FP.IEEE.Software
open Interchange

abbrev ExtendedReal := WithBot (WithTop ℚ)

/-- Ordered exact values: infinities are endpoints and NaNs have no ordered value. -/
def orderedValue {I : Interchange} (d : Datum I) : Option ExtendedReal :=
  match d with
  | .quietNaN .. | .signalingNaN .. => none
  | .infinity s => some (if s then ⊥ else ↑(⊤ : WithTop ℚ))
  | _ => some (↑(↑d.fields.rationalValue : WithTop ℚ))

def compareDatum {I J : Interchange} (a : Datum I) (b : Datum J) : Option Ordering :=
  match orderedValue a, orderedValue b with
  | some x, some y => some (compareOfLessAndEq x y)
  | _, _ => none

/-- A truth table on the four outcomes, covering every IEEE comparison predicate. -/
structure Relation where
  less : Bool
  equal : Bool
  greater : Bool
  unordered : Bool
  deriving DecidableEq, Repr

namespace Relation

def holds (r : Relation) : Option Ordering → Bool
  | some .lt => r.less
  | some .eq => r.equal
  | some .gt => r.greater
  | none => r.unordered

def eq : Relation := ⟨false, true, false, false⟩
def ne : Relation := ⟨true, false, true, true⟩
def lt : Relation := ⟨true, false, false, false⟩
def le : Relation := ⟨true, true, false, false⟩
def gt : Relation := ⟨false, false, true, false⟩
def ge : Relation := ⟨false, true, true, false⟩
def ordered : Relation := ⟨true, true, true, false⟩
def isUnordered : Relation := ⟨false, false, false, true⟩
def lessGreater : Relation := ⟨true, false, true, false⟩
def unorderedEqual : Relation := ⟨false, true, false, true⟩
def unorderedLess : Relation := ⟨true, false, false, true⟩
def unorderedLessEqual : Relation := ⟨true, true, false, true⟩
def unorderedGreater : Relation := ⟨false, false, true, true⟩
def unorderedGreaterEqual : Relation := ⟨false, true, true, true⟩
end Relation

inductive ComparisonMode where
  | quiet | signaling
  deriving DecidableEq, Repr

def comparisonInvalid {I J : Interchange} (mode : ComparisonMode)
    (a : Datum I) (b : Datum J) : Bool :=
  match mode with
  | .quiet => a.isSignaling || b.isSignaling
  | .signaling => a.isNaN || b.isNaN

def compare (I J : Interchange) (mode : ComparisonMode) (relation : Relation)
    (a : I.Word) (b : J.Word) : Result Bool :=
  let da := Datum.decode I a
  let db := Datum.decode J b
  ⟨relation.holds (compareDatum da db),
    fun e => (e == .invalid) && comparisonInvalid mode da db⟩

def classify (I : Interchange) (w : I.Word) : Datum.Class := (Datum.decode I w).classify
def isFinite (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isFinite
def isNaN (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isNaN
def isSignaling (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isSignaling
def isInfinite (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isInfinite
def isZero (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isZero
def isNormal (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isNormal
def isSubnormal (I : Interchange) (w : I.Word) : Bool := (Datum.decode I w).isSubnormal
def isSignMinus (I : Interchange) (w : I.Word) : Bool := I.negative w

/-- Binary interchange encodings have no redundant, noncanonical encodings.
This differs from the native Lean model's additional NaN-canonicalization rule. -/
def isCanonical (_I : Interchange) (_w : _I.Word) : Bool := true

def radix (_I : Interchange) : Nat := 2

theorem orderedValue_none {I : Interchange} (d : Datum I) :
    (orderedValue d).isNone = d.isNaN := by cases d <;> rfl

theorem orderedValue_of_toRat {I : Interchange} (d : Datum I) (x : ℚ)
    (h : d.toRat? = some x) : orderedValue d = some (↑(↑x : WithTop ℚ)) := by
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite, orderedValue]

theorem compareDatum_unordered {I J : Interchange} (a : Datum I) (b : Datum J) :
    (compareDatum a b).isNone = (a.isNaN || b.isNaN) := by
  have ha := orderedValue_none a
  have hb := orderedValue_none b
  unfold compareDatum
  cases h1 : orderedValue a <;> cases h2 : orderedValue b <;> simp_all

theorem compareDatum_finite {I J : Interchange} (a : Datum I) (b : Datum J) (x y : ℚ)
    (ha : a.toRat? = some x) (hb : b.toRat? = some y) :
    compareDatum a b = some (compareOfLessAndEq x y) := by
  simp only [compareDatum, orderedValue_of_toRat a x ha, orderedValue_of_toRat b y hb]
  simp [compareOfLessAndEq]

/-- Numeric equality of either signed zero with either signed zero. -/
theorem compareDatum_zeros (I J : Interchange) (s t : Bool) :
    compareDatum (Datum.zero (I := I) s) (Datum.zero (I := J) t) = some .eq := by
  rw [compareDatum_finite _ _ 0 0 (Datum.toRat?_zero I s) (Datum.toRat?_zero J t)]
  rfl

theorem compare_invalid (I J : Interchange) (mode : ComparisonMode) (r : Relation)
    (a : I.Word) (b : J.Word) :
    (compare I J mode r a b).flags .invalid =
      comparisonInvalid mode (Datum.decode I a) (Datum.decode J b) := by
  simp [compare]

theorem compare_other_flags (I J : Interchange) (mode : ComparisonMode) (r : Relation)
    (a : I.Word) (b : J.Word) (e : Exception) (he : e ≠ .invalid) :
    (compare I J mode r a b).flags e = false := by
  simp [compare, he]

/-- Comparison values follow the independent ordered-value interpretation and
selected truth table. The flag policy has no influence on this value. -/
theorem compare_value (I J : Interchange) (mode : ComparisonMode) (r : Relation)
    (a : I.Word) (b : J.Word) :
    (compare I J mode r a b).value =
      r.holds (compareDatum (Datum.decode I a) (Datum.decode J b)) := rfl

theorem compare_quiet_signaling_value (I J : Interchange) (r : Relation)
    (a : I.Word) (b : J.Word) :
    (compare I J .quiet r a b).value = (compare I J .signaling r a b).value := rfl

theorem isFinite_spec (I : Interchange) [I.Valid] (w : I.Word) :
    isFinite I w = true ↔ I.IsFinite w := by
  rw [isFinite, Datum.isFinite_iff]
  simpa only [Datum.decode, Datum.fields_ofFields, Fields.pack_unpack] using
    (Fields.isFinite_pack (Fields.unpack I w)).symm

end FP.IEEE.Software
