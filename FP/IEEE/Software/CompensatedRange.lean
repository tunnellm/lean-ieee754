import FP.IEEE.Software.CompensatedInput

/-! Explicit operation-range conditions for complete compensated summation. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Three exact inputs must stay below the nearest-even overflow threshold:
the high addition, `bvirt`, and the correction addition. Subnormals are allowed. -/
def CompensatedStepRange (I : Interchange) [I.Valid] (s c a : I.Word) : Prop :=
  (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true ∧
  (Datum.decode I a).isFinite = true ∧
  |(wordRat I s : ℝ)+(wordRat I a : ℝ)| < I.format.overflowThreshold ∧
  |I.format.roundFinite ((wordRat I s : ℝ)+(wordRat I a : ℝ))-(wordRat I s : ℝ)| <
    I.format.overflowThreshold ∧
  |(wordRat I c : ℝ)+((wordRat I s : ℝ)+(wordRat I a : ℝ)-
    I.format.roundFinite ((wordRat I s : ℝ)+(wordRat I a : ℝ)))| < I.format.overflowThreshold

def CompensatedPassRange (I : Interchange) [I.Valid] (s c : I.Word) : List I.Word → Prop
  | [] => (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true
  | a::xs => CompensatedStepRange I s c a ∧
      CompensatedPassRange I (twoSum I s a).value.1
        (add I .nearestEven c (twoSum I s a).value.2).value xs

/-- The final addition needs its own range condition, after a finite pass. -/
def CompensatedSumRange (I : Interchange) [I.Valid] (xs : List I.Word) : Prop :=
  CompensatedPassRange I (Datum.zero false).encode (Datum.zero false).encode xs ∧
  |(wordRat I (compensatedCore I (Datum.zero false).encode (Datum.zero false).encode xs).value.1 : ℝ)+
    (wordRat I (compensatedCore I (Datum.zero false).encode (Datum.zero false).encode xs).value.2 : ℝ)| <
    I.format.overflowThreshold

private theorem wordRat_decode_of_finite (I : Interchange) (w : I.Word)
    (h : (Datum.decode I w).isFinite = true) :
    (Datum.decode I w).toRat? = some (wordRat I w) := by
  simp [Datum.toRat?,wordRat,h]

private theorem finite_of_real_decode (I : Interchange) [I.Valid] (w : I.Word) (x : ℝ)
    (h : I.decode? w = some x) : (Datum.decode I w).isFinite = true := by
  have hd := Datum.toRat?_decode I w
  rw [h] at hd
  obtain ⟨q,hq,_⟩ := Option.map_eq_some_iff.mp hd
  have hf := congrArg Option.isSome hq
  simpa only [Datum.toRat?_isSome,Option.isSome_some] using hf

private theorem add_finite_of_range (I : Interchange) [I.Valid] (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (h : |(x : ℝ)+(y : ℝ)| < I.format.overflowThreshold) :
    (Datum.decode I (add I .nearestEven a b).value).isFinite = true := by
  apply finite_of_real_decode I _ (I.format.roundFinite ((x : ℝ)+(y : ℝ)))
  simpa [add,Spec.binaryExact,Format.round?,h] using binary_even_cast I .add a b x y ha hb

theorem CompensatedStepRange.toFinite (I : Interchange) [I.Valid] (s c a : I.Word)
    (h : CompensatedStepRange I s c a) : CompensatedStepFinite I s c a := by
  obtain ⟨hs,hc,ha,hadd,hbv,hcorr⟩ := h
  have hsd := wordRat_decode_of_finite I s hs
  have hcd := wordRat_decode_of_finite I c hc
  have had := wordRat_decode_of_finite I a ha
  have ht := certifiedTwoSum?_of_range I s a _ _ hsd had hadd hbv
  have hf := (certifiedTwoSum?_success_iff_finite_stages I s a).mp ht
  have he := (twoSum_exact_of_range I s a _ _ hsd had hadd hbv).2
  have hed := Datum.toRat?_decode I (twoSum I s a).value.2
  rw [he] at hed
  obtain ⟨e,heq,heval⟩ := Option.map_eq_some_iff.mp hed
  refine ⟨hs,hc,ha,hf.2.2.1,hf.2.2.2,?_⟩
  exact add_finite_of_range I c (twoSum I s a).value.2 _ e hcd heq (by simpa [heval] using hcorr)

theorem CompensatedPassRange.toFinite (I : Interchange) [I.Valid] (xs : List I.Word) (s c : I.Word)
    (h : CompensatedPassRange I s c xs) : CompensatedPassFinite I s c xs := by
  induction xs generalizing s c with
  | nil => exact h
  | cons a xs ih => exact ⟨CompensatedStepRange.toFinite I s c a h.1,ih _ _ h.2⟩

theorem CompensatedPassFinite.result_finite (I : Interchange) [I.Valid] (xs : List I.Word) (s c : I.Word)
    (h : CompensatedPassFinite I s c xs) :
    (Datum.decode I (compensatedCore I s c xs).value.1).isFinite = true ∧
    (Datum.decode I (compensatedCore I s c xs).value.2).isFinite = true := by
  induction xs generalizing s c with
  | nil => exact h
  | cons a xs ih =>
    simpa only [compensatedCore,Result.bind] using ih _ _ h.2

theorem CompensatedSumRange.toFinite (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumRange I xs) : CompensatedSumFinite I xs := by
  have hp := CompensatedPassRange.toFinite I xs _ _ h.1
  have hf := CompensatedPassFinite.result_finite I xs _ _ hp
  refine ⟨hp,?_⟩
  exact add_finite_of_range I _ _ _ _ (wordRat_decode_of_finite I _ hf.1)
    (wordRat_decode_of_finite I _ hf.2) h.2

theorem compensatedSum?_complete_of_range (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumRange I xs) : ∃ r, compensatedSum? I xs = some r :=
  compensatedSum?_complete I xs (CompensatedSumRange.toFinite I xs h)

theorem compensatedSum_mixed_of_range (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumRange I xs) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff xs.length)^2*(wordListAbsSum I xs : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff xs.length)*
            geomWeight I.format.unitRoundoff xs.length)+I.format.minSubnormal/2 :=
  compensatedSum_mixed_of_finite I xs (CompensatedSumRange.toFinite I xs h)

theorem compensatedSum_gamma_of_range (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumRange I xs) (hn : xs.length*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff xs.length)^2*(wordListAbsSum I xs : ℝ)+
          xs.length*(I.format.minSubnormal/2)/(1-xs.length*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 :=
  compensatedSum_gamma_of_finite I xs (CompensatedSumRange.toFinite I xs h) hn

end FP.IEEE.Software
