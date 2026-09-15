import FP.IEEE.Software.RoundingModes

/-! Default overflow delivery for all rounding modes. This handler assumes its
caller has detected overflow; the unconditional result/flag theorem does not
assert that an arbitrary caller should signal overflow. -/
namespace FP.IEEE.Software
open Interchange

theorem maxFinite_pos (F : Format) : 0 < maxFinite F := by
  have hp : (1 : ℚ) ≤ 2 ^ F.fractionBits := one_le_pow₀ (by norm_num)
  unfold maxFinite
  rw [pow_succ]
  exact mul_pos (by linarith) (by positivity)

theorem signedMaxFinite_representable (F : Format) (negative : Bool) :
    F.Representable ((if negative then -maxFinite F else maxFinite F : ℚ) : ℝ) := by
  have hp : (1 : ℝ) ≤ 2 ^ (F.fractionBits + 1) := one_le_pow₀ (by norm_num)
  have hm : |(((2 : ℤ) ^ (F.fractionBits + 1) - 1 : ℤ) : ℝ)| <
      (2 : ℝ)^F.precision := by
    push_cast
    rw [abs_of_nonneg (by linarith), Format.precision]
    linarith
  cases negative
  · refine ⟨(2 : ℤ)^(F.fractionBits + 1) - 1, F.emax - F.fractionBits,
      sub_le_sub_right F.exponent_order _, le_rfl, hm, ?_⟩
    simp [maxFinite]
  · refine ⟨-((2 : ℤ)^(F.fractionBits + 1) - 1), F.emax - F.fractionBits,
      sub_le_sub_right F.exponent_order _, le_rfl, ?_, ?_⟩
    · rw [Int.cast_neg, abs_neg]; exact hm
    · simp only [ite_true, Rat.cast_neg, maxFinite_cast]
      unfold Format.maxFinite
      push_cast
      ring

def overflowToInfinity (mode : RoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearestEven | .nearestAway => true
  | .towardZero => false
  | .towardPositive => !negative
  | .towardNegative => negative

theorem overflowToInfinity_spec (mode : RoundingMode) (negative : Bool) :
    overflowToInfinity mode negative = true ↔ Spec.OverflowToInfinity mode negative := by
  cases mode <;> cases negative <;> simp [overflowToInfinity, Spec.OverflowToInfinity]

def overflowResult (I : Interchange) (mode : RoundingMode) (negative : Bool) : Result I.Word :=
  ⟨if overflowToInfinity mode negative then (Datum.infinity negative).encode
   else encodeFinite I (if negative then -maxFinite I.format else maxFinite I.format)
     negative (signedMaxFinite_representable I.format negative),
   fun e => match e with
     | .overflow | .inexact => true
     | _ => false⟩

/-- Default delivery: signed infinity or signed largest finite value, with
exactly overflow and inexact newly raised. -/
theorem overflowResult_spec (I : Interchange) [I.Valid] (mode : RoundingMode) (negative : Bool) :
    (Spec.OverflowToInfinity mode negative →
      Datum.decode I (overflowResult I mode negative).value = .infinity negative) ∧
    (¬ Spec.OverflowToInfinity mode negative →
      I.decode? (overflowResult I mode negative).value =
        some (if negative then -I.format.maxFinite else I.format.maxFinite)) ∧
    I.negative (overflowResult I mode negative).value = negative ∧
    (∀ e, (overflowResult I mode negative).flags e = true ↔
      e = .overflow ∨ e = .inexact) := by
  have hp := maxFinite_pos I.format
  have hs : valueSign (if negative then -maxFinite I.format else maxFinite I.format) negative = negative := by
    cases negative <;> simp [valueSign, ne_of_gt hp, ne_of_lt (neg_neg_of_pos hp), hp, not_lt.mpr hp.le]
  have hv := encodeFinite_spec I
    (if negative then -maxFinite I.format else maxFinite I.format) negative
    (signedMaxFinite_representable I.format negative)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp [overflowResult, (overflowToInfinity_spec mode negative).mpr h]
  · intro h
    have hh : overflowToInfinity mode negative = false := by
      cases hc : overflowToInfinity mode negative
      · rfl
      · exact (h ((overflowToInfinity_spec mode negative).mp hc)).elim
    cases negative <;> simpa [overflowResult, hh] using hv.1
  · unfold overflowResult
    dsimp only
    by_cases h : overflowToInfinity mode negative = true
    · simp [h, Datum.encode, Datum.fields]
    · simpa [h] using hv.2.trans hs
  · intro e; cases e <;> simp [overflowResult]

end FP.IEEE.Software
