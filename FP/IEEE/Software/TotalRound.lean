import FP.IEEE.Software.ModeRepresentation

/-! Total all-mode rounding to interchange words, including default flags.
The input is an exact rational; arithmetic special operands are handled by
future operation-specific wrappers. -/
namespace FP.IEEE.Software
open Interchange

/-- Round an exact finite input in any supported mode. `zeroSign` selects the
sign of an exact zero input. Inexact zeros inherit the exact input's sign. -/
def roundWithMode (I : Interchange) (mode : RoundingMode) (x : ℚ)
    (zeroSign : Bool := false) : Result I.Word :=
  ⟨if h : overflowWithMode I.format mode x = true then
      (overflowResult I mode (valueSign x zeroSign)).value
    else encodeFinite I (scaledRound I.format mode x) (valueSign x zeroSign)
      (scaledRound_representable I.format mode x (Bool.eq_false_iff.mpr h)),
    roundingFlags I.format mode x⟩

/-- Unconditional refinement for every rational input and every rounding mode.
No caller assumption of nonoverflow or representability is required. -/
theorem roundWithMode_spec (I : Interchange) [I.Valid] (mode : RoundingMode)
    (x : ℚ) (zeroSign : Bool) :
    Spec.Rounding I mode (x : ℝ) zeroSign (roundWithMode I mode x zeroSign) := by
  classical
  have hc := overflowWithMode_spec I.format mode x
  by_cases ho : overflowWithMode I.format mode x = true
  · have hs := overflowResult_spec I mode (valueSign x zeroSign)
    have hr := hc.mp ho
    constructor
    · intro h; exact (h hr).elim
    · intro _ h
      simpa [roundWithMode, ho, valueSign_cast] using
        hs.1 (by simpa [valueSign_cast] using h)
    · intro _ h
      simpa [roundWithMode, ho, valueSign_cast] using
        hs.2.1 (by simpa [valueSign_cast] using h)
    · simpa [roundWithMode, ho, hr, valueSign_cast] using hs.2.2.1
    · exact roundingFlags_spec I.format mode x
  · have hn := Bool.eq_false_iff.mpr ho
    have hr : ¬ Spec.OverflowWithMode I.format mode (x : ℝ) := fun h => ho (hc.mpr h)
    have hv := encodeFinite_spec I (scaledRound I.format mode x) (valueSign x zeroSign)
      (scaledRound_representable I.format mode x hn)
    constructor
    · intro _
      simpa [roundWithMode, ho, scaledRound_cast] using hv.1
    · intro h; exact (hr h).elim
    · intro h; exact (hr h).elim
    · simpa [roundWithMode, ho, hr, valueSign_cast, scaledRound_cast] using hv.2
    · exact roundingFlags_spec I.format mode x

/-- Decoding a nonoverflowing result recovers the rational lattice rounder. -/
theorem roundWithMode_projection (I : Interchange) [I.Valid] (mode : RoundingMode)
    (x : ℚ) (zeroSign : Bool) (ho : overflowWithMode I.format mode x = false) :
    (Datum.decode I (roundWithMode I mode x zeroSign).value).toRat? =
      some (scaledRound I.format mode x) := by
  have hr := (roundWithMode_spec I mode x zeroSign).finite
    (by simpa [← overflowWithMode_spec] using ho)
  have ha := (Datum.toRat?_decode I (roundWithMode I mode x zeroSign).value).trans hr
  rw [← scaledRound_cast] at ha
  exact (Option.map_injective Rat.cast_injective) ha

/-- Complementary error theorem on actual result words, valid through underflow.
Only the absence of overflow is needed for the finite numerical bound. -/
theorem roundWithMode_mixed_error (I : Interchange) [I.Valid] (mode : RoundingMode)
    (x : ℚ) (zeroSign : Bool) (ho : overflowWithMode I.format mode x = false) :
    ∃ y : ℝ, I.decode? (roundWithMode I mode x zeroSign).value = some y ∧
      |y - (x : ℝ)| ≤ (2 * I.format.unitRoundoff) * |(x : ℝ)| + I.format.minSubnormal := by
  refine ⟨(scaledRound I.format mode x : ℝ), ?_, scaledRound_mixed_error I.format mode x⟩
  rw [scaledRound_cast]
  exact (roundWithMode_spec I mode x zeroSign).finite
    (by simpa [← overflowWithMode_spec] using ho)

end FP.IEEE.Software
