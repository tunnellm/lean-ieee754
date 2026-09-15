import FP.IEEE.Software.Arithmetic
import FP.IEEE.Spec.Conversion

/-! Cross-format conversion, with no host floating-point operations. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Align payload high bits; widening appends zeros, narrowing discards low bits. -/
def alignedPayload (s d p : ℕ) : ℕ := p * 2^d / 2^s

theorem alignedPayload_lt (s d p : ℕ) (hp : p < 2^s) : alignedPayload s d p < 2^d := by
  unfold alignedPayload
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^s)).mpr
  nlinarith [show 0 < 2^d by positivity]

def convertNaN (S D : Interchange) [D.Valid] (d : Datum S) : D.Word :=
  (makeQuietNaN D d.fields.negative (BitVec.ofNat D.format.fractionBits
    (alignedPayload (S.format.fractionBits - 1) (D.format.fractionBits - 1)
      (S.payload d.fields.fraction).toNat))).encode

theorem convertNaN_spec (S D : Interchange) [D.Valid] (d : Datum S) :
    Spec.ConvertedNaN S D d (convertNaN S D d) := by
  have hp := alignedPayload_lt (S.format.fractionBits - 1) (D.format.fractionBits - 1)
    (S.payload d.fields.fraction).toNat (BitVec.isLt _)
  have hf : alignedPayload (S.format.fractionBits - 1) (D.format.fractionBits - 1)
      (S.payload d.fields.fraction).toNat < 2^D.format.fractionBits :=
    hp.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  constructor
  · simp [convertNaN, makeQuietNaN, Datum.classify]
  · simp [convertNaN, makeQuietNaN, Datum.fields]
  · simp only [convertNaN, Datum.decode_encode, makeQuietNaN, Datum.fields, quietFraction_payload]
    change (alignedPayload (S.format.fractionBits - 1) (D.format.fractionBits - 1)
      (S.payload d.fields.fraction).toNat % 2^D.format.fractionBits) %
        2^(D.format.fractionBits - 1) = alignedPayload (S.format.fractionBits - 1)
          (D.format.fractionBits - 1) (S.payload d.fields.fraction).toNat
    rw [Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hp]

def convert (S D : Interchange) [D.Valid] (mode : RoundingMode) (w : S.Word) : Result D.Word :=
  let d := Datum.decode S w
  if d.isNaN then
    ⟨convertNaN S D d, fun e => (e == .invalid) && d.isSignaling⟩
  else if d.isInfinite then Result.pure (Datum.infinity d.fields.negative).encode
  else roundWithMode D mode d.fields.rationalValue d.fields.negative

theorem convert_spec (S D : Interchange) [D.Valid] (mode : RoundingMode) (w : S.Word) :
    Spec.Conversion S D mode w (convert S D mode w) := by
  unfold Spec.Conversion convert
  dsimp only
  split_ifs
  · refine ⟨convertNaN_spec S D _, ?_, ?_⟩
    · simp
    · intro e he; simp [he]
  · simp [Result.pure]
  · have h := roundWithMode_spec D mode (Datum.decode S w).fields.rationalValue
      (Datum.decode S w).fields.negative
    rw [Fields.rationalValue_cast] at h
    change Spec.Rounding D mode (S.value (Datum.decode S w).encode)
      (Datum.decode S w).fields.negative _ at h
    simpa only [Datum.encode_decode] using h

theorem convert_finite (S D : Interchange) [D.Valid] (mode : RoundingMode) (w : S.Word) (q : ℚ)
    (h : (Datum.decode S w).toRat? = some q) :
    convert S D mode w = roundWithMode D mode q (Datum.decode S w).fields.negative := by
  have hd : ∀ d : Datum S, d.toRat? = some q →
      d.isNaN = false ∧ d.isInfinite = false ∧ d.fields.rationalValue = q := by
    intro d; cases d <;> simp_all [Datum.toRat?, Datum.isFinite, Datum.isNaN, Datum.isInfinite]
  obtain ⟨hn, hi, hv⟩ := hd _ h
  simp [convert, hn, hi, hv]

/-- Nearest-even finite conversion recovers the destination's existing finite model. -/
theorem convert_even_projection (S D : Interchange) [D.Valid] (w : S.Word) (q : ℚ)
    (h : (Datum.decode S w).toRat? = some q) :
    (Datum.decode D (convert S D .nearestEven w).value).toRat? = roundNearest? D.format q := by
  rw [convert_finite S D .nearestEven w q h]
  exact roundWithMode_even_projection D q _

/-- Widening preserves the high payload and appends low zero bits. -/
theorem alignedPayload_widen (s d p : ℕ) (h : s ≤ d) :
    alignedPayload s d p = p * 2^(d - s) := by
  have he : (2 : ℕ)^d = 2^(d - s) * 2^s := by rw [← pow_add]; congr 1; omega
  simp [alignedPayload, he, ← Nat.mul_assoc]

/-- A narrow-wide-narrow payload conversion loses no original payload bits. -/
theorem alignedPayload_roundtrip (s d p : ℕ) (h : s ≤ d) :
    alignedPayload d s (alignedPayload s d p) = p := by
  rw [alignedPayload_widen s d p h]
  unfold alignedPayload
  have he : p * 2^(d - s) * 2^s = p * 2^d := by
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  rw [he]
  simp

/-- The actual NaN converter preserves payloads through widening and narrowing.
Signaling NaNs are quieted; this theorem concerns their diagnostic payload. -/
theorem convertNaN_payload_roundtrip (S D : Interchange) [S.Valid] [D.Valid] (d : Datum S)
    (h : S.format.fractionBits ≤ D.format.fractionBits) :
    (S.payload (Datum.decode S (convertNaN D S (Datum.decode D (convertNaN S D d)))).fields.fraction).toNat =
      (S.payload d.fields.fraction).toNat := by
  rw [(convertNaN_spec D S (Datum.decode D (convertNaN S D d))).payload,
    (convertNaN_spec S D d).payload]
  exact alignedPayload_roundtrip (S.format.fractionBits - 1) (D.format.fractionBits - 1)
    _ (by omega)

end FP.IEEE.Software
