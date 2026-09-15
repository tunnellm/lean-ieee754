import FP.Range.Compensated
import FP.IEEE.Software.CompensatedRange
import FP.IEEE.Software.CompensatedDotRange

/-! Sound interval transformers for the actual IEEE compensated operations. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange FP.Range

/-- Finite word containment. In particular, exceptional words cannot masquerade as zero. -/
def WordIn (I : Interchange) (J : Interval) (w : I.Word) : Prop :=
  (Datum.decode I w).isFinite = true ∧ J.Contains (wordRat I w : ℝ)

theorem WordIn.of_decode (I : Interchange) [I.Valid] {J : Interval} {w : I.Word} {x : ℝ}
    (hd : I.decode? w = some x) (hx : J.Contains x) : WordIn I J w := by
  have h := Datum.toRat?_decode I w
  rw [hd] at h
  obtain ⟨q,hq,_⟩ := Option.map_eq_some_iff.mp h
  exact ⟨finite_of_toRat I w q hq, by simpa [wordRat_cast_of_decode I w x hd] using hx⟩

theorem WordIn.decode (I : Interchange) [I.Valid] {J : Interval} {w : I.Word}
    (h : WordIn I J w) : I.decode? w = some (wordRat I w : ℝ) := by
  rw [← Datum.toRat?_decode, finite_toRat_wordRat I w h.1]
  rfl

theorem WordIn.zero (I : Interchange) [I.Valid] :
    WordIn I .zero (Datum.zero false).encode := by
  simp [WordIn, Interval.Contains, Interval.zero, wordRat, Datum.isFinite,
    Datum.fields, Fields.rationalValue]

theorem add_zero_zero_decode (I : Interchange) [I.Valid] :
    I.decode? (add I .nearestEven (Datum.zero false).encode (Datum.zero false).encode).value = some 0 := by
  have hz : (Datum.decode I (Datum.zero false).encode).toRat? = some 0 := by
    simp [Datum.toRat?,Datum.isFinite,Datum.fields,Fields.rationalValue]
  simpa [add,Spec.binaryExact,Format.round?,I.format.overflowThreshold_pos] using
    binary_even_cast I .add (Datum.zero false).encode (Datum.zero false).encode 0 0 hz hz

theorem checkBinary_word_sound (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) {J K : Interval}
    (ha : (Datum.decode I a).isFinite = true) (hb : (Datum.decode I b).isFinite = true)
    (hj : J.Contains (binaryExact op (wordRat I a) (wordRat I b) : ℝ))
    (hc : checkRound (.ofFormat I.format) J = some K) :
    |(binaryExact op (wordRat I a) (wordRat I b) : ℝ)| < I.format.overflowThreshold ∧
      WordIn I K (binary I op .nearestEven a b).value := by
  obtain ⟨hr,hk⟩ := checkRound_sound I.format hj hc
  have had := finite_toRat_wordRat I a ha
  have hbd := finite_toRat_wordRat I b hb
  have hf := binary_even_finite_of_real_range I op a b _ _ had hbd hr
  have hv := binary_even_roundFinite_of_decode I op a b _ _ _ had hbd
    (finite_toRat_wordRat I _ hf)
  exact ⟨hr,hf,by simpa [hv] using hk⟩

theorem checkAdd_word_sound (I : Interchange) [I.Valid] (a b : I.Word) {A B K : Interval}
    (ha : WordIn I A a) (hb : WordIn I B b)
    (hc : checkRound (.ofFormat I.format) (A.add B) = some K) :
    |(wordRat I a : ℝ)+(wordRat I b : ℝ)| < I.format.overflowThreshold ∧
      WordIn I K (add I .nearestEven a b).value := by
  simpa only [add, binaryExact, Rat.cast_add] using checkBinary_word_sound I .add a b ha.1 hb.1
    (by simpa only [binaryExact, Rat.cast_add] using Interval.contains_add ha.2 hb.2) hc

theorem add_wordRat_roundFinite (I : Interchange) [I.Valid] (a b : I.Word)
    (ha : (Datum.decode I a).isFinite = true) (hb : (Datum.decode I b).isFinite = true)
    (hc : (Datum.decode I (add I .nearestEven a b).value).isFinite = true) :
    (wordRat I (add I .nearestEven a b).value : ℝ) =
      I.format.roundFinite ((wordRat I a : ℝ)+(wordRat I b : ℝ)) := by
  simpa only [add,binaryExact,Rat.cast_add] using binary_even_roundFinite_of_decode I .add a b _ _ _
    (finite_toRat_wordRat I a ha) (finite_toRat_wordRat I b hb) (finite_toRat_wordRat I _ hc)

theorem checkTwoSum_word_sound (I : Interchange) [I.Valid] (s a : I.Word)
    {S A : Interval} {r : Interval × Interval} (hs : WordIn I S s) (ha : WordIn I A a)
    (hc : checkTwoSum (.ofFormat I.format) S A = some r) :
    |(wordRat I s : ℝ)+(wordRat I a : ℝ)| < I.format.overflowThreshold ∧
    |I.format.roundFinite ((wordRat I s : ℝ)+(wordRat I a : ℝ))-(wordRat I s : ℝ)| <
      I.format.overflowThreshold ∧
    WordIn I r.1 (twoSum I s a).value.1 ∧ WordIn I r.2 (twoSum I s a).value.2 := by
  have hvalid := And.intro (Interval.valid_of_contains hs.2) (Interval.valid_of_contains ha.2)
  simp only [checkTwoSum, if_pos hvalid] at hc
  change (checkRound (.ofFormat I.format) (S.add A)).bind _ = some r at hc
  obtain ⟨H,hH,hrest⟩ := Option.bind_eq_some_iff.mp hc
  split_ifs at hrest with hb
  cases Option.some.inj hrest
  obtain ⟨hadd,hhigh⟩ := checkAdd_word_sound I s a hs ha hH
  have he := roundErrorBound_sound I.format (Interval.contains_add hs.2 ha.2)
  have hvirt := Interval.contains_inflate ha.2 (show
      |(I.format.roundFinite ((wordRat I s : ℝ)+(wordRat I a : ℝ))-(wordRat I s : ℝ))-
        (wordRat I a : ℝ)| ≤ (roundErrorBound (.ofFormat I.format) (S.add A) : ℝ) by
    simpa only [sub_sub] using he)
  have hbvirt := interval_range I.format hvirt hb
  have ht := twoSum_exact_of_range I s a _ _ (finite_toRat_wordRat I s hs.1)
    (finite_toRat_wordRat I a ha.1) hadd hbvirt
  refine ⟨hadd,hbvirt,hhigh,WordIn.of_decode I ht.2 ?_⟩
  apply Interval.contains_symmetric
  simpa only [abs_sub_comm] using he

theorem checkTwoProduct_word_sound (I : Interchange) [I.Valid] (a b : I.Word)
    {A B : Interval} {r : Interval × Interval} (ha : WordIn I A a) (hb : WordIn I B b)
    (hc : checkTwoProduct (.ofFormat I.format) A B = some r) :
    |(wordRat I a : ℝ)*(wordRat I b : ℝ)| < I.format.overflowThreshold ∧
    WordIn I r.1 (twoProduct I a b).value.1 ∧ WordIn I r.2 (twoProduct I a b).value.2 := by
  have hvalid := And.intro (Interval.valid_of_contains ha.2) (Interval.valid_of_contains hb.2)
  simp only [checkTwoProduct, if_pos hvalid] at hc
  change (checkRound (.ofFormat I.format) (A.mul B)).bind _ = some r at hc
  obtain ⟨H,hH,hr⟩ := Option.bind_eq_some_iff.mp hc
  cases Option.some.inj hr
  obtain ⟨hp,hhigh⟩ := checkBinary_word_sound I .mul a b ha.1 hb.1
    (by simpa only [binaryExact,Rat.cast_mul] using Interval.contains_mul ha.2 hb.2) hH
  change WordIn I H (mul I .nearestEven a b).value at hhigh
  have had := finite_toRat_wordRat I a ha.1
  have hbd := finite_toRat_wordRat I b hb.1
  have hpd := finite_toRat_wordRat I _ hhigh.1
  obtain ⟨e,hed,hdef⟩ := twoProduct_bounded_of_finite I a b _ _ _ had hbd hpd
  have hpr := binary_even_roundFinite_of_decode I .mul a b _ _ _ had hbd hpd
  have he := roundErrorBound_sound I.format (Interval.contains_mul ha.2 hb.2)
  simp only [binaryExact,Rat.cast_mul] at hp hpr
  simp only [Rat.cast_sub,Rat.cast_mul] at hdef
  have hlow : |(e : ℝ)| ≤ (roundErrorBound (.ofFormat I.format) (A.mul B) : ℝ)+I.format.minSubnormal/2 := by
    have hh := abs_add_le ((wordRat I a : ℝ)*(wordRat I b : ℝ)-
      (wordRat I (mul I .nearestEven a b).value : ℝ))
      (-((wordRat I a : ℝ)*(wordRat I b : ℝ)-
        (wordRat I (mul I .nearestEven a b).value : ℝ)-(e : ℝ)))
    rw [show (wordRat I a : ℝ)*(wordRat I b : ℝ)-
      (wordRat I (mul I .nearestEven a b).value : ℝ)+
      (-((wordRat I a : ℝ)*(wordRat I b : ℝ)-
        (wordRat I (mul I .nearestEven a b).value : ℝ)-(e : ℝ))) = (e : ℝ) by ring,
      abs_neg] at hh
    have herr : |(wordRat I a : ℝ)*(wordRat I b : ℝ)-
      (wordRat I (mul I .nearestEven a b).value : ℝ)| ≤
      (roundErrorBound (.ofFormat I.format) (A.mul B) : ℝ) := by
      simpa [hpr,abs_sub_comm] using he
    linarith
  refine ⟨hp,hhigh,finite_of_toRat I _ e hed,?_⟩
  apply Interval.contains_symmetric
  simpa only [twoProduct,wordRat_of_decode I _ e hed,Rat.cast_add,Params.ofFormat_ε] using hlow

/-- Both accumulator words are finite and enclosed. -/
def StateIn (I : Interchange) (st : CompensatedState) (s c : I.Word) : Prop :=
  WordIn I st.high s ∧ WordIn I st.correction c

theorem StateIn.zero (I : Interchange) [I.Valid] :
    StateIn I .zero (Datum.zero false).encode (Datum.zero false).encode :=
  ⟨WordIn.zero I,WordIn.zero I⟩

theorem checkCompensatedStep_word_sound (I : Interchange) [I.Valid] (s c a : I.Word)
    {st out : CompensatedState} {A : Interval} (hs : StateIn I st s c) (ha : WordIn I A a)
    (hc : checkCompensatedStep (.ofFormat I.format) st A = some out) :
    CompensatedStepRange I s c a ∧
      StateIn I out (twoSum I s a).value.1 (add I .nearestEven c (twoSum I s a).value.2).value := by
  simp only [checkCompensatedStep,if_pos (Interval.valid_of_contains hs.2.2)] at hc
  change (checkTwoSum (.ofFormat I.format) st.high A).bind _ = some out at hc
  obtain ⟨h,hh,hrest⟩ := Option.bind_eq_some_iff.mp hc
  change (checkRound (.ofFormat I.format) (st.correction.add h.2)).bind _ = some out at hrest
  obtain ⟨C,hC,hout⟩ := Option.bind_eq_some_iff.mp hrest
  cases Option.some.inj hout
  obtain ⟨hadd,hbv,hhigh,hlow⟩ := checkTwoSum_word_sound I s a hs.1 ha hh
  obtain ⟨hcorr,hcorrV⟩ := checkAdd_word_sound I c _ hs.2 hlow hC
  have hv := wordRat_cast_of_decode I _ _ (twoSum_exact_of_range I s a _ _
    (finite_toRat_wordRat I s hs.1.1) (finite_toRat_wordRat I a ha.1) hadd hbv).2
  refine ⟨⟨hs.1.1,hs.2.1,ha.1,hadd,hbv,?_⟩,hhigh,hcorrV⟩
  simpa only [hv] using hcorr

theorem compensatedDotStep_value (I : Interchange) [I.Valid] (s c a b : I.Word) :
    (compensatedDotStep I s c a b).value =
      ((twoSum I s (twoProduct I a b).value.1).value.1,
       (add I .nearestEven c (add I .nearestEven (twoProduct I a b).value.2
         (twoSum I s (twoProduct I a b).value.1).value.2).value).value) := rfl

theorem checkCompensatedDotStep_word_sound (I : Interchange) [I.Valid] (s c a b : I.Word)
    {st out : CompensatedState} {A B : Interval}
    (hs : StateIn I st s c) (ha : WordIn I A a) (hb : WordIn I B b)
    (hc : checkCompensatedDotStep (.ofFormat I.format) st A B = some out) :
    CompensatedDotStepRange I s c a b ∧
      StateIn I out (compensatedDotStep I s c a b).value.1 (compensatedDotStep I s c a b).value.2 := by
  simp only [checkCompensatedDotStep,if_pos (Interval.valid_of_contains hs.2.2)] at hc
  change (checkTwoProduct (.ofFormat I.format) A B).bind _ = some out at hc
  obtain ⟨p,hp,hrest⟩ := Option.bind_eq_some_iff.mp hc
  change (checkTwoSum (.ofFormat I.format) st.high p.1).bind _ = some out at hrest
  obtain ⟨h,hh,hrest⟩ := Option.bind_eq_some_iff.mp hrest
  change (checkRound (.ofFormat I.format) (p.2.add h.2)).bind _ = some out at hrest
  obtain ⟨T,hT,hrest⟩ := Option.bind_eq_some_iff.mp hrest
  change (checkRound (.ofFormat I.format) (st.correction.add T)).bind _ = some out at hrest
  obtain ⟨C,hC,hout⟩ := Option.bind_eq_some_iff.mp hrest
  cases Option.some.inj hout
  obtain ⟨hpRange,hprod,hprodLow⟩ := checkTwoProduct_word_sound I a b ha hb hp
  obtain ⟨hhRange,hbvRange,hhigh,hlow⟩ := checkTwoSum_word_sound I s _ hs.1 hprod hh
  obtain ⟨htRange,ht⟩ := checkAdd_word_sound I _ _ hprodLow hlow hT
  obtain ⟨hcRange,hcorr⟩ := checkAdd_word_sound I c _ hs.2 ht hC
  have hσ := wordRat_cast_of_decode I _ _ (twoSum_exact_of_range I s _ _ _
    (finite_toRat_wordRat I s hs.1.1) (finite_toRat_wordRat I _ hprod.1) hhRange hbvRange).2
  have htr := add_wordRat_roundFinite I _ _ hprodLow.1 hlow.1 ht.1
  rw [hσ] at htr
  have hrange : CompensatedDotStepRange I s c a b := by
    refine ⟨hs.1.1,hs.2.1,ha.1,hb.1,hpRange,hhRange,hbvRange,?_,?_⟩
    · simpa only [hσ] using htRange
    · simpa only [htr] using hcRange
  refine ⟨hrange,?_⟩
  rw [compensatedDotStep_value]
  exact ⟨hhigh,hcorr⟩

theorem checkCompensatedFinish_word_sound (I : Interchange) [I.Valid] (s c : I.Word)
    {st : CompensatedState} {J : Interval} (hs : StateIn I st s c)
    (hc : checkCompensatedFinish (.ofFormat I.format) st = some J) :
    |(wordRat I s : ℝ)+(wordRat I c : ℝ)| < I.format.overflowThreshold ∧
      WordIn I J (add I .nearestEven s c).value := by
  have hv := And.intro (Interval.valid_of_contains hs.1.2) (Interval.valid_of_contains hs.2.2)
  exact checkAdd_word_sound I s c hs.1 hs.2 (by simpa only [checkCompensatedFinish,if_pos hv] using hc)

end FP.IEEE.Software
