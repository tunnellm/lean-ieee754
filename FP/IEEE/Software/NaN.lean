import FP.IEEE.Software.Comparison

/-! Deterministic NaN construction and operand propagation. Operation-specific
invalid conditions (such as zero times infinity) remain the caller's responsibility. -/
namespace FP.IEEE.Software
open Interchange

/-- Set the quiet bit while retaining all payload bits. -/
def quietFraction (I : Interchange) (f : BitVec I.format.fractionBits) :
    BitVec I.format.fractionBits :=
  f ||| BitVec.ofNat I.format.fractionBits (2 ^ (I.format.fractionBits - 1))

theorem quietFraction_quiet (I : Interchange) [I.Valid]
    (f : BitVec I.format.fractionBits) : I.quietBit (quietFraction I f) = true := by
  have hp := Valid.fraction_pos (I := I)
  simp [quietFraction, Interchange.quietBit, BitVec.getLsbD_ofNat,
    show I.format.fractionBits - 1 < I.format.fractionBits by omega]

theorem quietFraction_nonzero (I : Interchange) [I.Valid]
    (f : BitVec I.format.fractionBits) : quietFraction I f ≠ 0#I.format.fractionBits := by
  intro h
  have hh := quietFraction_quiet I f
  rw [h] at hh
  simp [Interchange.quietBit] at hh

/-- Quieting changes no payload bit. -/
theorem quietFraction_payload (I : Interchange) (f : BitVec I.format.fractionBits) :
    I.payload (quietFraction I f) = I.payload f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmask : (BitVec.ofNat I.format.fractionBits
      (2 ^ (I.format.fractionBits - 1))).getLsbD i = false := by
    simp [BitVec.getLsbD_ofNat, Ne.symm (Nat.ne_of_lt hi)]
  simp only [Interchange.payload, quietFraction, BitVec.getLsbD_extractLsb',
    Nat.zero_add, BitVec.getLsbD_or, hmask, Bool.or_false]

@[simp] theorem quietFraction_idempotent (I : Interchange)
    (f : BitVec I.format.fractionBits) :
    quietFraction I (quietFraction I f) = quietFraction I f := by
  simp [quietFraction, BitVec.or_assoc]

def makeQuietNaN (I : Interchange) [I.Valid] (negative : Bool)
    (fraction : BitVec I.format.fractionBits) : Datum I :=
  .quietNaN negative (quietFraction I fraction)
    (quietFraction_nonzero I fraction) (quietFraction_quiet I fraction)

def defaultNaN (I : Interchange) [I.Valid] : Datum I := makeQuietNaN I false 0

/-- First signaling operand, otherwise first quiet operand. -/
def selectNaN {I : Interchange} (operands : List (Datum I)) : Option (Datum I) :=
  match operands.find? Datum.isSignaling with
  | some d => some d
  | none => operands.find? Datum.isNaN

/-- Propagate a NaN operand, or produce the default quiet NaN when no NaN occurs.
This helper records signaling-input invalid only; callers add other exceptions. -/
def propagateNaN (I : Interchange) [I.Valid] (operands : List (Datum I)) : Result (Datum I) :=
  let result := match selectNaN operands with
    | some d => makeQuietNaN I d.fields.negative d.fields.fraction
    | none => defaultNaN I
  ⟨result, fun e => (e == .invalid) && operands.any Datum.isSignaling⟩

theorem propagateNaN_quiet (I : Interchange) [I.Valid] (operands : List (Datum I)) :
    (propagateNaN I operands).value.classify = .quietNaN := by
  unfold propagateNaN
  cases selectNaN operands <;> rfl

theorem propagateNaN_invalid (I : Interchange) [I.Valid] (operands : List (Datum I)) :
    (propagateNaN I operands).flags .invalid = operands.any Datum.isSignaling := by
  simp [propagateNaN]

theorem propagateNaN_other_flags (I : Interchange) [I.Valid] (operands : List (Datum I))
    (e : Exception) (he : e ≠ .invalid) :
    (propagateNaN I operands).flags e = false := by
  simp [propagateNaN, he]

theorem propagateNaN_selected (I : Interchange) [I.Valid] (operands : List (Datum I))
    (d : Datum I) (h : selectNaN operands = some d) :
    (propagateNaN I operands).value.fields.negative = d.fields.negative ∧
    I.payload (propagateNaN I operands).value.fields.fraction = I.payload d.fields.fraction := by
  simp [propagateNaN, h, makeQuietNaN, Datum.fields, quietFraction_payload]

end FP.IEEE.Software
