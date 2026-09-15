import FP.IEEE.Software.RangeOperations
import FP.Range.CompensatedBounds

/-! Whole-domain interval and accuracy guarantees for compensated summation. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange FP.Range

theorem checkCompensatedPass_word_sound (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word}
    (hb : List.Forall₂ (WordIn I) bounds xs) (s c : I.Word)
    {st out : CompensatedState} (hs : StateIn I st s c)
    (hc : checkCompensatedPass (.ofFormat I.format) st bounds = some out) :
    CompensatedPassRange I s c xs ∧
      StateIn I out (compensatedCore I s c xs).value.1 (compensatedCore I s c xs).value.2 := by
  induction hb generalizing s c st out with
  | nil =>
    have hv := And.intro (Interval.valid_of_contains hs.1.2) (Interval.valid_of_contains hs.2.2)
    have he : st = out := Option.some.inj (by simpa only [checkCompensatedPass,if_pos hv] using hc)
    subst out
    exact ⟨⟨hs.1.1,hs.2.1⟩,hs⟩
  | @cons A a bounds xs ha hb ih =>
    change (checkCompensatedStep (.ofFormat I.format) st A).bind _ = some out at hc
    obtain ⟨t,ht,hrest⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨hr,hs'⟩ := checkCompensatedStep_word_sound I s c a hs ha ht
    obtain ⟨hpass,hout⟩ := ih _ _ hs' hrest
    exact ⟨⟨hr,hpass⟩,hout⟩

theorem checkCompensatedSum_range_sound (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} (hb : List.Forall₂ (WordIn I) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    CompensatedSumRange I xs ∧ WordIn I r.resultInterval (compensatedSum I xs).value := by
  by_cases hz : bounds = []
  · subst bounds
    cases hb
    have hr : AccuracyCertificate.zero = r := Option.some.inj (by simpa [checkCompensatedSum] using hc)
    subst r
    refine ⟨?_,WordIn.of_decode I (add_zero_zero_decode I) Interval.contains_zero⟩
    simp [CompensatedSumRange,CompensatedPassRange,compensatedCore,Result.pure,
      wordRat,Datum.isFinite,Datum.fields,Fields.rationalValue,I.format.overflowThreshold_pos]
  · simp only [checkCompensatedSum,if_neg hz] at hc
    change (checkCompensatedPass (.ofFormat I.format) .zero bounds).bind _ = some r at hc
    obtain ⟨st,hst,hrest⟩ := Option.bind_eq_some_iff.mp hc
    change (checkCompensatedFinish (.ofFormat I.format) st).bind _ = some r at hrest
    obtain ⟨J,hJ,hr⟩ := Option.bind_eq_some_iff.mp hrest
    cases Option.some.inj hr
    obtain ⟨hp,hstate⟩ := checkCompensatedPass_word_sound I hb _ _ (StateIn.zero I) hst
    obtain ⟨hf,hout⟩ := checkCompensatedFinish_word_sound I _ _ hstate hJ
    exact ⟨⟨hp,hf⟩,hout⟩

theorem wordIn_sum_bounds (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} (hb : List.Forall₂ (WordIn I) bounds xs) :
    (exactSumInterval bounds).Contains (wordListSum I xs : ℝ) ∧
      (wordListAbsSum I xs : ℝ) ≤ (sumIntervalMass bounds : ℝ) := by
  induction hb with
  | nil => exact ⟨by simpa [exactSumInterval,wordListSum] using Interval.contains_zero,by simp [wordListAbsSum,sumIntervalMass]⟩
  | @cons A a bounds xs ha hb ih =>
    refine ⟨by simpa [exactSumInterval,wordListSum] using Interval.contains_add ha.2 ih.1,?_⟩
    simpa [wordListAbsSum,sumIntervalMass] using add_le_add (Interval.abs_le_radius ha.2) ih.2

theorem checkCompensatedSum_sound (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} (hb : List.Forall₂ (WordIn I) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    CompensatedSumFinite I xs ∧ ∃ q : ℝ,
      I.decode? (compensatedSum I xs).value = some q ∧ r.resultInterval.Contains q ∧
      r.exactInterval.Contains (wordListSum I xs : ℝ) ∧
      |q-(wordListSum I xs : ℝ)| ≤ (r.errorBound : ℝ) := by
  obtain ⟨hr,hout⟩ := checkCompensatedSum_range_sound I hb hc
  have hf := CompensatedSumRange.toFinite I xs hr
  refine ⟨hf,?_⟩
  by_cases hz : bounds = []
  · subst bounds
    cases hb
    have he : AccuracyCertificate.zero = r := Option.some.inj (by simpa [checkCompensatedSum] using hc)
    subst r
    exact ⟨0,add_zero_zero_decode I,Interval.contains_zero,by simpa [wordListSum,AccuracyCertificate.zero] using Interval.contains_zero,by simp [wordListSum,AccuracyCertificate.zero]⟩
  · obtain ⟨q,hq,herr⟩ := compensatedSum_mixed_of_finite I xs hf
    obtain ⟨hT,hM⟩ := wordIn_sum_bounds I hb
    have hbound := sumAccuracyBound_sound I.format _ _ _ _ _ xs.length hT hM herr
    have hlen := hb.length_eq
    simp only [checkCompensatedSum,if_neg hz] at hc
    change (checkCompensatedPass (.ofFormat I.format) .zero bounds).bind _ = some r at hc
    obtain ⟨st,_,hrest⟩ := Option.bind_eq_some_iff.mp hc
    change (checkCompensatedFinish (.ofFormat I.format) st).bind _ = some r at hrest
    obtain ⟨J,_,he⟩ := Option.bind_eq_some_iff.mp hrest
    cases Option.some.inj he
    refine ⟨q,hq,?_,hT,by simpa only [hlen] using hbound⟩
    simpa only [wordRat_cast_of_decode I _ q hq] using hout.2

theorem compensatedSum_complete_of_range_certificate (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} (hb : List.Forall₂ (WordIn I) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    ∃ c, compensatedSum? I xs = some c :=
  compensatedSum?_complete I xs (checkCompensatedSum_sound I hb hc).1

theorem compensatedSum_enclosure_of_range_certificate (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} (hb : List.Forall₂ (WordIn I) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    ∃ J, compensatedEnclosure? I xs = some J ∧ J.Contains (wordListSum I xs : ℝ) :=
  compensatedEnclosure?_exists_of_finite I xs (checkCompensatedSum_sound I hb hc).1

end FP.IEEE.Software
