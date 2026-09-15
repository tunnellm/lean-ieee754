import FP.IEEE.Software.FiniteEncoding
import FP.IEEE.Spec.Nearest

/-! Total executable nearest-even rounding from exact rational inputs to IEEE
result words and default exception flags. No native Float operation is used. -/
namespace FP.IEEE.Software
open Interchange

def precisionRound (F : Format) (x : ℚ) : ℚ :=
  let h := (2 : ℚ) ^ (Int.log 2 |x| - F.fractionBits)
  (roundInt .nearestEven (x / h) : ℚ) * h

def tinyAfter (F : Format) (x : ℚ) : Bool :=
  decide (0 < |precisionRound F x| ∧ |precisionRound F x| < (2 : ℚ)^F.emin)

private def finiteRoundingFlags (F : Format) (x y : ℚ) : Flags
  | .invalid | .divideByZero | .overflow => false
  | .inexact => decide (y ≠ x)
  | .underflow => decide (y ≠ x) && tinyAfter F x

private def overflowRoundingFlags : Flags
  | .overflow | .inexact => true
  | _ => false

/-- Round an exact finite input, returning actual result bits and newly raised flags.
The explicit zero sign is used for an exact zero input; a nonzero input rounded
to zero retains its sign. Both zero signs are permitted by the exact encoder. -/
def roundNearest (I : Interchange) (x : ℚ) (zeroSign : Bool := false) : Result I.Word :=
  if h : |x| < overflowThreshold I.format then
    let y := scaledRound I.format .nearestEven x
    let hy : I.format.Representable (y : ℝ) :=
      roundNearest?_representable I.format x y (by simp [roundNearest?, h, y])
    ⟨encodeFinite I y (valueSign x zeroSign) hy, finiteRoundingFlags I.format x y⟩
  else
    ⟨(Datum.infinity (I := I) (valueSign x zeroSign)).encode, overflowRoundingFlags⟩

theorem precisionRound_cast (F : Format) (x : ℚ) :
    (precisionRound F x : ℝ) = Spec.precisionRound F (x : ℝ) := by
  unfold precisionRound Spec.precisionRound
  rw [log_abs_cast]
  dsimp only
  rw [roundInt_even_equiv]
  push_cast
  rfl

theorem tinyAfter_spec (F : Format) (x : ℚ) :
    tinyAfter F x = true ↔ Spec.TinyAfter F (x : ℝ) := by
  unfold tinyAfter Spec.TinyAfter Format.minNormal
  rw [← precisionRound_cast]
  have hlo := Rat.cast_lt (K := ℝ) (p := 0) (q := |precisionRound F x|)
  have hhi := Rat.cast_lt (K := ℝ) (p := |precisionRound F x|) (q := (2 : ℚ)^F.emin)
  simpa only [decide_eq_true_eq, Rat.cast_zero, Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat] using
    (and_congr hlo hhi).symm

theorem valueSign_cast (x : ℚ) (s : Bool) : valueSign x s = Spec.realSign (x : ℝ) s := by
  classical
  simp only [valueSign, Spec.realSign, Rat.cast_eq_zero, Rat.cast_lt_zero]

/-- Independent real specification refinement: values, signs, overflow words,
and every default exception flag. -/
theorem roundNearest_spec (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool) :
    Spec.NearestRounding I (x : ℝ) zeroSign (roundNearest I x zeroSign) := by
  have hc : |(x : ℝ)| < I.format.overflowThreshold ↔ |x| < overflowThreshold I.format := by
    rw [← overflowThreshold_cast]
    simpa only [Rat.cast_abs] using
      (Rat.cast_lt (K := ℝ) (p := |x|) (q := overflowThreshold I.format))
  have he : scaledRound I.format .nearestEven x ≠ x ↔ I.format.roundFinite (x : ℝ) ≠ (x : ℝ) := by
    rw [← scaledRound_even_cast]
    exact not_congr Rat.cast_inj.symm
  unfold roundNearest
  split_ifs with hr
  · let y := scaledRound I.format .nearestEven x
    have hy : I.format.Representable (y : ℝ) :=
      roundNearest?_representable I.format x y (by simp [roundNearest?, hr, y])
    have hv := encodeFinite_spec I y (valueSign x zeroSign) hy
    constructor
    · exact hv.1.trans (by simp [Format.round?, hc, hr, y, scaledRound_even_cast])
    · simpa [hc, hr, valueSign_cast, y, scaledRound_even_cast] using hv.2
    · intro h; exact (h (hc.mpr hr)).elim
    · rfl
    · rfl
    · simp [finiteRoundingFlags, hc, hr]
    · simp [finiteRoundingFlags, hc, hr, he]
    · simp [finiteRoundingFlags, hc, hr, he, tinyAfter_spec]
  · constructor
    · simp [Datum.encode, Datum.fields, Interchange.decode?, Format.round?, hc, hr]
    · simp [Datum.encode, Datum.fields, hc, hr, valueSign_cast]
    · intro _; simp [valueSign_cast]
    · rfl
    · rfl
    · simp [overflowRoundingFlags, hc, hr]
    · simp [overflowRoundingFlags, hc, hr]
    · simp [overflowRoundingFlags, hc, hr]

/-- The total word rounder projects to the previous finite rational rounder. -/
theorem roundNearest_projection (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool) :
    (Datum.decode I (roundNearest I x zeroSign).value).toRat? = roundNearest? I.format x := by
  have ha := (Datum.toRat?_decode I (roundNearest I x zeroSign).value).trans
    (roundNearest_spec I x zeroSign).value
  have hb := roundNearest?_cast I.format x
  have hmap := ha.trans hb.symm
  exact (Option.map_injective Rat.cast_injective) hmap

end FP.IEEE.Software
