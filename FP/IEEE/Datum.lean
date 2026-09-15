import FP.IEEE.Fields

/-! A total, lossless view of IEEE binary encodings. Constructor invariants rule
out zero subnormal significands, reserved normal exponents, and zero NaNs. -/
set_option backward.isDefEq.respectTransparency false

namespace FP.IEEE.Interchange

@[simp] theorem allOnes_ne_zero (I : Interchange) [I.Valid] :
    BitVec.allOnes I.exponentBits ≠ 0 := by
  change BitVec.allOnes I.exponentBits ≠ 0#I.exponentBits
  rw [Ne, BitVec.allOnes_eq_zero_iff]
  exact Nat.ne_of_gt (Valid.exponent_pos (I := I))

/-- The quiet bit is part of the fraction; the remaining low bits are the payload. -/
def quietBit (I : Interchange) (f : BitVec I.format.fractionBits) : Bool :=
  f.getLsbD (I.format.fractionBits - 1)

def payload (I : Interchange) (f : BitVec I.format.fractionBits) :
    BitVec (I.format.fractionBits - 1) := f.extractLsb' 0 _

inductive Datum (I : Interchange) where
  | zero (negative : Bool)
  | subnormal (negative : Bool) (fraction : BitVec I.format.fractionBits)
      (nonzero : fraction ≠ 0#I.format.fractionBits)
  | normal (negative : Bool) (exponent : BitVec I.exponentBits)
      (fraction : BitVec I.format.fractionBits)
      (nonzero : exponent ≠ 0#I.exponentBits) (notMax : exponent ≠ BitVec.allOnes I.exponentBits)
  | infinity (negative : Bool)
  | quietNaN (negative : Bool) (fraction : BitVec I.format.fractionBits)
      (nonzero : fraction ≠ 0#I.format.fractionBits) (quiet : I.quietBit fraction = true)
  | signalingNaN (negative : Bool) (fraction : BitVec I.format.fractionBits)
      (nonzero : fraction ≠ 0#I.format.fractionBits) (signaling : I.quietBit fraction = false)

namespace Datum

def fields {I : Interchange} : Datum I → Fields I
  | .zero s => ⟨s, 0, 0⟩
  | .subnormal s f _ => ⟨s, 0, f⟩
  | .normal s e f _ _ => ⟨s, e, f⟩
  | .infinity s => ⟨s, BitVec.allOnes _, 0⟩
  | .quietNaN s f _ _ => ⟨s, BitVec.allOnes _, f⟩
  | .signalingNaN s f _ _ => ⟨s, BitVec.allOnes _, f⟩

def ofFields {I : Interchange} (f : Fields I) : Datum I :=
  if he : f.exponent = BitVec.allOnes _ then
    if hf : f.fraction = 0 then .infinity f.negative
    else if hq : I.quietBit f.fraction = true then .quietNaN f.negative f.fraction hf hq
    else .signalingNaN f.negative f.fraction hf (by simpa using hq)
  else if he0 : f.exponent = 0 then
    if hf : f.fraction = 0 then .zero f.negative
    else .subnormal f.negative f.fraction hf
  else .normal f.negative f.exponent f.fraction he0 he

@[simp] theorem fields_ofFields {I : Interchange} (f : Fields I) :
    (ofFields f).fields = f := by
  rcases f with ⟨s, e, m⟩
  unfold ofFields
  split <;> rename_i he
  · split <;> rename_i hm
    · simp_all [fields]
    · split <;> simp_all [fields]
  · split <;> rename_i hz
    · split <;> rename_i hm
      · simp_all [fields]
      · simp_all [fields]
    · rfl

@[simp] theorem ofFields_fields {I : Interchange} [I.Valid] (d : Datum I) :
    ofFields d.fields = d := by
  have hp := Nat.ne_of_gt (Valid.exponent_pos (I := I))
  cases d <;> simp_all [fields, ofFields, BitVec.ofNat_eq_ofNat]

def encode {I : Interchange} (d : Datum I) : I.Word := d.fields.pack

def decode (I : Interchange) (w : I.Word) : Datum I := ofFields (Fields.unpack I w)

@[simp] theorem encode_decode (I : Interchange) (w : I.Word) :
    (decode I w).encode = w := by simp [decode, encode]

@[simp] theorem decode_encode {I : Interchange} [I.Valid] (d : Datum I) :
    decode I d.encode = d := by simp [decode, encode]

theorem encode_injective {I : Interchange} [I.Valid] :
    Function.Injective (encode (I := I)) := by
  intro a b h
  simpa using congrArg (decode I) h

/-- All IEEE classification results, retaining the sign distinction for non-NaNs. -/
inductive Class where
  | signalingNaN | quietNaN | negativeInfinity | negativeNormal | negativeSubnormal
  | negativeZero | positiveZero | positiveSubnormal | positiveNormal | positiveInfinity
  deriving DecidableEq, Repr

def classify {I : Interchange} : Datum I → Class
  | .zero s => if s then .negativeZero else .positiveZero
  | .subnormal s .. => if s then .negativeSubnormal else .positiveSubnormal
  | .normal s .. => if s then .negativeNormal else .positiveNormal
  | .infinity s => if s then .negativeInfinity else .positiveInfinity
  | .quietNaN .. => .quietNaN
  | .signalingNaN .. => .signalingNaN

def isFinite {I : Interchange} : Datum I → Bool
  | .zero .. | .subnormal .. | .normal .. => true
  | _ => false

def isNaN {I : Interchange} : Datum I → Bool
  | .quietNaN .. | .signalingNaN .. => true
  | _ => false

def isSignaling {I : Interchange} : Datum I → Bool
  | .signalingNaN .. => true
  | _ => false

def isInfinite {I : Interchange} : Datum I → Bool
  | .infinity .. => true
  | _ => false

def isZero {I : Interchange} : Datum I → Bool
  | .zero .. => true
  | _ => false

def isNormal {I : Interchange} : Datum I → Bool
  | .normal .. => true
  | _ => false

def isSubnormal {I : Interchange} : Datum I → Bool
  | .subnormal .. => true
  | _ => false

/-- Quiet sign operations change neither NaN type nor payload. -/
def withSign {I : Interchange} (d : Datum I) (s : Bool) : Datum I :=
  match d with
  | .zero _ => .zero s
  | .subnormal _ f h => .subnormal s f h
  | .normal _ e f h hm => .normal s e f h hm
  | .infinity _ => .infinity s
  | .quietNaN _ f h hq => .quietNaN s f h hq
  | .signalingNaN _ f h hq => .signalingNaN s f h hq

@[simp] theorem fields_withSign {I : Interchange} (d : Datum I) (s : Bool) :
    (d.withSign s).fields = d.fields.withSign s := by cases d <;> rfl
@[simp] theorem withSign_self {I : Interchange} (d : Datum I) :
    d.withSign d.fields.negative = d := by cases d <;> rfl
@[simp] theorem withSign_withSign {I : Interchange} (d : Datum I) (s t : Bool) :
    (d.withSign s).withSign t = d.withSign t := by cases d <;> rfl
@[simp] theorem isNaN_withSign {I : Interchange} (d : Datum I) (s : Bool) :
    (d.withSign s).isNaN = d.isNaN := by cases d <;> rfl
@[simp] theorem isSignaling_withSign {I : Interchange} (d : Datum I) (s : Bool) :
    (d.withSign s).isSignaling = d.isSignaling := by cases d <;> rfl

theorem isFinite_iff {I : Interchange} [I.Valid] (d : Datum I) :
    d.isFinite = true ↔ d.fields.exponent ≠ BitVec.allOnes I.exponentBits := by
  have hp := Nat.ne_of_gt (Valid.exponent_pos (I := I))
  cases d <;> simp_all [isFinite, fields, BitVec.ofNat_eq_ofNat]

end Datum
end FP.IEEE.Interchange
