import FP.IEEE.Software.RangeOperations
import FP.Range.CompensatedBounds
import FP.IEEE.Software.CompensatedDotList

/-! Input-domain certificates for the actual total online Dot2 execution. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange FP.Range
open scoped BigOperators

theorem checkCompensatedDotPass_word_sound (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i))
    {st : CompensatedState} (hc : checkCompensatedDotPass (.ofFormat I.format) A B n = some st) :
    CompensatedDotPassRange I a b n ∧
      StateIn I st (compensatedDotCore I a b n).value.1 (compensatedDotCore I a b n).value.2 := by
  induction n generalizing st with
  | zero =>
    have he : CompensatedState.zero = st := Option.some.inj hc
    subst st
    exact ⟨trivial,StateIn.zero I⟩
  | succ n ih =>
    change (checkCompensatedDotPass (.ofFormat I.format) A B n).bind _ = some st at hc
    obtain ⟨prev,hprev,hstep⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨hp,hs⟩ := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)) hprev
    obtain ⟨hr,hout⟩ := checkCompensatedDotStep_word_sound I _ _ (a n) (b n) hs
      (ha n (by omega)) (hb n (by omega)) hstep
    exact ⟨⟨hp,hr⟩,hout⟩

theorem checkCompensatedDot_range_sound (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    CompensatedDotRange I a b n ∧ WordIn I r.resultInterval (compensatedDot I a b n).value := by
  by_cases hz : n = 0
  · subst n
    have he : AccuracyCertificate.zero = r := Option.some.inj (by simpa [checkCompensatedDot] using hc)
    subst r
    refine ⟨?_,WordIn.of_decode I (add_zero_zero_decode I) Interval.contains_zero⟩
    simp [CompensatedDotRange,CompensatedDotPassRange,compensatedDotCore,Result.pure,
      wordRat,Datum.fields,Fields.rationalValue,I.format.overflowThreshold_pos]
  · simp only [checkCompensatedDot,if_neg hz] at hc
    change (checkCompensatedDotPass (.ofFormat I.format) A B n).bind _ = some r at hc
    obtain ⟨st,hst,hrest⟩ := Option.bind_eq_some_iff.mp hc
    change (checkCompensatedFinish (.ofFormat I.format) st).bind _ = some r at hrest
    obtain ⟨J,hJ,hr⟩ := Option.bind_eq_some_iff.mp hrest
    cases Option.some.inj hr
    obtain ⟨hp,hstate⟩ := checkCompensatedDotPass_word_sound I A B a b n ha hb hst
    obtain ⟨hf,hout⟩ := checkCompensatedFinish_word_sound I _ _ hstate hJ
    exact ⟨⟨hp,hf⟩,hout⟩

theorem wordIn_dot_bounds (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i)) :
    (exactDotInterval A B n).Contains (wordDotSum I a b n : ℝ) ∧
      (wordDotAbsSum I a b n : ℝ) ≤ (dotIntervalMass A B n : ℝ) := by
  simpa [wordDotSum,wordDotAbsSum] using exactDotInterval_sound A B
    (fun i => (wordRat I (a i) : ℝ)) (fun i => (wordRat I (b i) : ℝ)) n
    (fun i hi => (ha i hi).2) (fun i hi => (hb i hi).2)

theorem checkCompensatedDot_sound (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    CompensatedDotFinite I a b n ∧ ∃ q : ℝ,
      I.decode? (compensatedDot I a b n).value = some q ∧ r.resultInterval.Contains q ∧
      r.exactInterval.Contains (wordDotSum I a b n : ℝ) ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ (r.errorBound : ℝ) := by
  obtain ⟨hr,hout⟩ := checkCompensatedDot_range_sound I A B a b n ha hb hc
  have hf := CompensatedDotRange.toFinite I a b n hr
  refine ⟨hf,?_⟩
  by_cases hz : n = 0
  · subst n
    have he : AccuracyCertificate.zero = r := Option.some.inj (by simpa [checkCompensatedDot] using hc)
    subst r
    exact ⟨0,add_zero_zero_decode I,Interval.contains_zero,by simpa [wordDotSum,AccuracyCertificate.zero] using Interval.contains_zero,by simp [wordDotSum,AccuracyCertificate.zero]⟩
  · obtain ⟨q,hq,herr⟩ := compensatedDot_mixed_of_finite I a b n hf
    obtain ⟨hT,hM⟩ := wordIn_dot_bounds I A B a b n ha hb
    have hbound := dotAccuracyBound_sound I.format _ _ _ _ _ n hT hM herr
    simp only [checkCompensatedDot,if_neg hz] at hc
    change (checkCompensatedDotPass (.ofFormat I.format) A B n).bind _ = some r at hc
    obtain ⟨st,_,hrest⟩ := Option.bind_eq_some_iff.mp hc
    change (checkCompensatedFinish (.ofFormat I.format) st).bind _ = some r at hrest
    obtain ⟨J,_,he⟩ := Option.bind_eq_some_iff.mp hrest
    cases Option.some.inj he
    refine ⟨q,hq,?_,hT,hbound⟩
    simpa only [wordRat_cast_of_decode I _ q hq] using hout.2

theorem compensatedDot_complete_of_range_certificate (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    ∃ c, compensatedDot? I a b n = some c :=
  compensatedDot?_complete I a b n (checkCompensatedDot_sound I A B a b n ha hb hc).1

theorem compensatedDot_enclosure_of_range_certificate (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (n : ℕ)
    (ha : ∀ i < n, WordIn I (A i) (a i)) (hb : ∀ i < n, WordIn I (B i) (b i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    ∃ J, compensatedDotEnclosure? I a b n = some J ∧ J.Contains (wordDotSum I a b n : ℝ) :=
  compensatedDotEnclosure?_exists_of_finite I a b n (checkCompensatedDot_sound I A B a b n ha hb hc).1

end FP.IEEE.Software
