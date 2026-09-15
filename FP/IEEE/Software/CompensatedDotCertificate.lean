import FP.IEEE.Software.CompensatedDot
import FP.DotCompensation
import FP.Range.Interval

/-! Finite-execution certificates for Dot2. Product residuals may be inexact;
local rational accounting records their actual defects. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange
open scoped BigOperators

structure DotCompensationState (I : Interchange) where
  high : I.Word
  correction : I.Word
  radius : ℚ
  highLossMass : ℚ
  residualMass : ℚ
  productDefectMass : ℚ

def DotCompensationState.initial (I : Interchange) : DotCompensationState I :=
  ⟨(Datum.zero false).encode,(Datum.zero false).encode,0,0,0,0⟩

/-- FMA-residual and TwoSum-reconstruction finiteness follow from these checks. -/
def CompensatedDotStepFinite (I : Interchange) [I.Valid] (s c a b : I.Word) : Prop :=
  let t := dotStepTrace I s c a b
  (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true ∧
  (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
  (Datum.decode I t.product.value.1).isFinite = true ∧
  (Datum.decode I t.sum.sum.value).isFinite = true ∧
  (Datum.decode I t.sum.bvirt.value).isFinite = true ∧
  (Datum.decode I t.combined.value).isFinite = true ∧
  (Datum.decode I t.correction.value).isFinite = true

instance (I : Interchange) [I.Valid] (s c a b : I.Word) : Decidable (CompensatedDotStepFinite I s c a b) := by
  unfold CompensatedDotStepFinite; infer_instance

def dotCompensationUpdate (I : Interchange) [I.Valid] (st : DotCompensationState I) (a b : I.Word) : DotCompensationState I :=
  let t := dotStepTrace I st.high st.correction a b
  let v := wordRat I a*wordRat I b
  let p := wordRat I t.product.value.1
  let π := wordRat I t.product.value.2
  let σ := wordRat I t.sum.error.value
  let z := wordRat I t.combined.value
  let c := wordRat I t.correction.value
  ⟨t.sum.sum.value,t.correction.value,
    st.radius+|z-(π+σ)|+|c-(wordRat I st.correction+z)|,
    st.highLossMass+|v-p|+|σ|,st.residualMass+|π|+|σ|,st.productDefectMass+|v-p-π|⟩

def compensatedDotStep? (I : Interchange) [I.Valid] (st : DotCompensationState I) (a b : I.Word) :
    Option (Result (DotCompensationState I)) :=
  if CompensatedDotStepFinite I st.high st.correction a b then
    some ⟨dotCompensationUpdate I st a b,(compensatedDotStep I st.high st.correction a b).flags⟩
  else none

def compensatedDotPass? (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : ℕ → Option (Result (DotCompensationState I))
  | 0 => some (Result.pure (DotCompensationState.initial I))
  | n+1 => do
    let p ← compensatedDotPass? I a b n
    let r ← compensatedDotStep? I p.value (a n) (b n)
    some ⟨r.value,p.flags.union r.flags⟩

structure CompensatedDotCertificate (I : Interchange) where
  result : Result I.Word
  state : DotCompensationState I
  errorBound : ℚ

def compensatedDot? (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Option (CompensatedDotCertificate I) :=
  match compensatedDotPass? I a b n with
  | none => none
  | some p =>
    let q := add I .nearestEven p.value.high p.value.correction
    if (Datum.decode I q.value).isFinite then
      some ⟨⟨q.value,p.flags.union q.flags⟩,p.value,
        p.value.radius+p.value.productDefectMass+|wordRat I q.value-(wordRat I p.value.high+wordRat I p.value.correction)|⟩
    else none

def compensatedDotList? (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word)) : Option (CompensatedDotCertificate I) :=
  compensatedDot? I (fun i => (xs[i]?.getD (0,0)).1) (fun i => (xs[i]?.getD (0,0)).2) xs.length

def wordDotSum (I : Interchange) (a b : ℕ → I.Word) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, wordRat I (a i)*wordRat I (b i)

def wordDotAbsSum (I : Interchange) (a b : ℕ → I.Word) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, |wordRat I (a i)*wordRat I (b i)|

structure DotCompensationState.Valid (I : Interchange) (st : DotCompensationState I) (T A : ℝ) (n : ℕ) : Prop where
  high_finite : (Datum.decode I st.high).toRat? = some (wordRat I st.high)
  correction_finite : (Datum.decode I st.correction).toRat? = some (wordRat I st.correction)
  accounting : FP.DotCompensationInvariant I.format.unitRoundoff (I.format.minSubnormal/2) T A
    (wordRat I st.high) (wordRat I st.correction) st.radius st.highLossMass st.residualMass st.productDefectMass n

theorem dot_compensation_initial_valid (I : Interchange) [I.Valid] :
    (DotCompensationState.initial I).Valid I 0 0 0 := by
  have hz : wordRat I (Datum.zero false).encode = 0 := by simp [wordRat,Datum.fields,Fields.rationalValue]
  constructor
  · simp [DotCompensationState.initial,hz]
  · simp [DotCompensationState.initial,hz]
  · simpa [DotCompensationState.initial,hz] using FP.dot_compensation_zero I.format.unitRoundoff (I.format.minSubnormal/2)

theorem compensatedDotStep?_success_iff_finite (I : Interchange) [I.Valid]
    (st : DotCompensationState I) (a b : I.Word) :
    (compensatedDotStep? I st a b).isSome = true ↔ CompensatedDotStepFinite I st.high st.correction a b := by
  simp [compensatedDotStep?]

theorem compensatedDotStep?_execution (I : Interchange) [I.Valid] (st : DotCompensationState I)
    (a b : I.Word) (r : Result (DotCompensationState I)) (hr : compensatedDotStep? I st a b = some r) :
    compensatedDotStep I st.high st.correction a b = ⟨(r.value.high,r.value.correction),r.flags⟩ := by
  unfold compensatedDotStep? at hr
  split_ifs at hr
  cases Option.some.inj hr
  rfl

theorem compensatedDotStep?_valid (I : Interchange) [I.Valid] (st : DotCompensationState I)
    (a b : I.Word) (T A : ℝ) (n : ℕ) (hv : st.Valid I T A n)
    (r : Result (DotCompensationState I)) (hr : compensatedDotStep? I st a b = some r) :
    r.value.Valid I (T+((wordRat I a*wordRat I b : ℚ) : ℝ))
      (A+|((wordRat I a*wordRat I b : ℚ) : ℝ)|) (n+1) := by
  unfold compensatedDotStep? at hr
  split_ifs at hr with hf
  cases Option.some.inj hr
  obtain ⟨hs,hc,ha,hb,hp,hh,hbv,ht,hd⟩ := hf
  have had := finite_toRat_wordRat I a ha
  have hbd := finite_toRat_wordRat I b hb
  have hpd := finite_toRat_wordRat I _ hp
  have hhd := finite_toRat_wordRat I _ hh
  have hbvd := finite_toRat_wordRat I _ hbv
  have htd := finite_toRat_wordRat I _ ht
  have hdd := finite_toRat_wordRat I _ hd
  obtain ⟨π,hπ,hdef⟩ := twoProduct_bounded_of_finite I a b _ _ _ had hbd hpd
  have wπ : wordRat I (dotStepTrace I st.high st.correction a b).product.value.2 = π := wordRat_of_decode I _ π hπ
  have hsplt := twoSum_exact_of_finite_stages I st.high (twoProduct I a b).value.1
    _ _ _ _ hv.high_finite hpd hhd hbvd
  have wσ : wordRat I (dotStepTrace I st.high st.correction a b).sum.error.value =
      wordRat I st.high+wordRat I (dotStepTrace I st.high st.correction a b).product.value.1-wordRat I (dotStepTrace I st.high st.correction a b).sum.sum.value :=
    wordRat_of_decode I _ _ hsplt.2
  have hpErr := binary_even_error_of_decode I .mul a b _ _ _ had hbd hpd
  have hsErr := binary_even_error_of_decode I .add st.high (twoProduct I a b).value.1 _ _ _ hv.high_finite hpd hhd
  have htErr := binary_even_error_of_decode I .add (twoProduct I a b).value.2
    (dotStepTrace I st.high st.correction a b).sum.error.value _ _ _ hπ hsplt.2 htd
  have hcErr := binary_even_error_of_decode I .add st.correction
    (dotStepTrace I st.high st.correction a b).combined.value _ _ _ hv.correction_finite htd hdd
  constructor
  · exact hhd
  · exact hdd
  · have he := FP.dot_compensation_step
      (v := ((wordRat I a*wordRat I b : ℚ) : ℝ))
      (p := (wordRat I (dotStepTrace I st.high st.correction a b).product.value.1 : ℝ))
      (π := (π : ℝ))
      (s' := (wordRat I (dotStepTrace I st.high st.correction a b).sum.sum.value : ℝ))
      (σ := ((wordRat I st.high+wordRat I (dotStepTrace I st.high st.correction a b).product.value.1-
        wordRat I (dotStepTrace I st.high st.correction a b).sum.sum.value : ℚ) : ℝ))
      (t := (wordRat I (dotStepTrace I st.high st.correction a b).combined.value : ℝ))
      (c' := (wordRat I (dotStepTrace I st.high st.correction a b).correction.value : ℝ))
      I.format.unitRoundoff_pos.le hv.accounting
      (by simpa [MixedError,binaryExact] using hpErr)
      (by push_cast; ring)
      (by simpa [MixedError,binaryExact] using hsErr)
      (by simpa only [Rat.cast_sub,Rat.cast_mul] using hdef)
      (by simpa [MixedError,binaryExact] using htErr)
      (by simpa [MixedError,binaryExact] using hcErr)
    simpa only [dotCompensationUpdate,wπ,wσ,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_abs] using he

theorem compensatedDotPass?_valid (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (r : Result (DotCompensationState I)) (hr : compensatedDotPass? I a b n = some r) :
    r.value.Valid I (wordDotSum I a b n : ℝ) (wordDotAbsSum I a b n : ℝ) n := by
  induction n generalizing r with
  | zero =>
    cases Option.some.inj hr
    simpa [wordDotSum,wordDotAbsSum,Result.pure] using dot_compensation_initial_valid I
  | succ n ih =>
    unfold compensatedDotPass? at hr
    cases hp : compensatedDotPass? I a b n with
    | none => simp [hp] at hr
    | some p =>
      cases ht : compensatedDotStep? I p.value (a n) (b n) with
      | none => simp [hp,ht] at hr
      | some t =>
        have he : (⟨t.value,p.flags.union t.flags⟩ : Result (DotCompensationState I)) = r := by simpa [hp,ht] using hr
        cases he
        have hv := compensatedDotStep?_valid I p.value (a n) (b n) _ _ n (ih p hp) t ht
        simpa [wordDotSum,wordDotAbsSum,Finset.sum_range_succ] using hv

theorem compensatedDotPass?_execution (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (r : Result (DotCompensationState I)) (hr : compensatedDotPass? I a b n = some r) :
    compensatedDotCore I a b n = ⟨(r.value.high,r.value.correction),r.flags⟩ := by
  induction n generalizing r with
  | zero => cases Option.some.inj hr; rfl
  | succ n ih =>
    unfold compensatedDotPass? at hr
    cases hp : compensatedDotPass? I a b n with
    | none => simp [hp] at hr
    | some p =>
      cases ht : compensatedDotStep? I p.value (a n) (b n) with
      | none => simp [hp,ht] at hr
      | some t =>
        have he : (⟨t.value,p.flags.union t.flags⟩ : Result (DotCompensationState I)) = r := by simpa [hp,ht] using hr
        cases he
        rw [compensatedDotCore,ih p hp]
        simp only [Result.bind]
        rw [compensatedDotStep?_execution I p.value (a n) (b n) t ht]

theorem compensatedDot?_execution (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (r : CompensatedDotCertificate I) (hr : compensatedDot? I a b n = some r) :
    compensatedDot I a b n = r.result := by
  unfold compensatedDot? at hr
  cases hp : compensatedDotPass? I a b n with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    rw [compensatedDot,compensatedDotPass?_execution I a b n p hp]
    rfl

end FP.IEEE.Software
