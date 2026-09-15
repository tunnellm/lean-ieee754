import FP.IEEE.Datum

namespace FP.IEEE.Interchange.Datum

/-- Exact, executable finite projection. Both zero signs map to zero;
infinities and both kinds of NaNs have no rational value. -/
def toRat? {I : Interchange} (d : Datum I) : Option ℚ :=
  if d.isFinite then some d.fields.rationalValue else none

/-- The lossless representation agrees with the original real-valued decoder. -/
theorem toRat?_cast {I : Interchange} [I.Valid] (d : Datum I) :
    d.toRat?.map (fun q : ℚ => (q : ℝ)) = I.decode? d.encode := by
  simp only [toRat?, encode, Interchange.decode?, Fields.isFinite_pack,
    ← isFinite_iff]
  split <;> simp [Fields.rationalValue_cast]

theorem toRat?_decode (I : Interchange) [I.Valid] (w : I.Word) :
    (decode I w).toRat?.map (fun q : ℚ => (q : ℝ)) = I.decode? w := by
  simpa using toRat?_cast (decode I w)

@[simp] theorem toRat?_zero (I : Interchange) (s : Bool) :
    (zero (I := I) s).toRat? = some 0 := by
  simp [toRat?, isFinite, fields, Fields.rationalValue]

@[simp] theorem toRat?_infinity (I : Interchange) (s : Bool) :
    (infinity (I := I) s).toRat? = none := rfl

theorem toRat?_isSome {I : Interchange} (d : Datum I) :
    d.toRat?.isSome = d.isFinite := by
  simp only [toRat?]
  cases h : d.isFinite <;> simp

end FP.IEEE.Interchange.Datum
