import FP.IEEE.Software.CompensatedDotBounds

/-! Analytical operation-range conditions and exact-product specializations for Dot2. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Exact real inputs to each potentially overflowing operation. The words used
in later conditions are finite as a consequence of the earlier conditions. -/
def CompensatedDotStepRange (I : Interchange) [I.Valid] (s c a b : I.Word) : Prop :=
  let p := twoProduct I a b
  let z : ℝ := (wordRat I s : ℝ)+(wordRat I p.value.1 : ℝ)
  let low : ℝ := (wordRat I p.value.2 : ℝ)+(z-I.format.roundFinite z)
  (Datum.decode I s).isFinite = true ∧ (Datum.decode I c).isFinite = true ∧
  (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
  |(wordRat I a : ℝ)*(wordRat I b : ℝ)| < I.format.overflowThreshold ∧
  |z| < I.format.overflowThreshold ∧ |I.format.roundFinite z-(wordRat I s : ℝ)| < I.format.overflowThreshold ∧
  |low| < I.format.overflowThreshold ∧ |(wordRat I c : ℝ)+I.format.roundFinite low| < I.format.overflowThreshold

def CompensatedDotPassRange (I : Interchange) [I.Valid] (a b : ℕ → I.Word) : ℕ → Prop
  | 0 => True
  | n+1 => CompensatedDotPassRange I a b n ∧
      CompensatedDotStepRange I (compensatedDotCore I a b n).value.1
        (compensatedDotCore I a b n).value.2 (a n) (b n)

def CompensatedDotRange (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Prop :=
  CompensatedDotPassRange I a b n ∧
    |(wordRat I (compensatedDotCore I a b n).value.1 : ℝ)+
      (wordRat I (compensatedDotCore I a b n).value.2 : ℝ)| < I.format.overflowThreshold

theorem CompensatedDotStepRange.toFinite (I : Interchange) [I.Valid] (s c a b : I.Word)
    (h : CompensatedDotStepRange I s c a b) : CompensatedDotStepFinite I s c a b := by
  obtain ⟨hs,hc,ha,hb,hp,hh,hbv,ht,hd⟩ := h
  have hsd := finite_toRat_wordRat I s hs
  have hcd := finite_toRat_wordRat I c hc
  have had := finite_toRat_wordRat I a ha
  have hbd := finite_toRat_wordRat I b hb
  have hpf := binary_even_finite_of_real_range I .mul a b _ _ had hbd (by simpa [binaryExact] using hp)
  have hpd := finite_toRat_wordRat I _ hpf
  have hπf := productResidual_isFinite I a b ha hb hpf
  have hπd := finite_toRat_wordRat I _ hπf
  have htwo := certifiedTwoSum?_of_range I s (twoProduct I a b).value.1 _ _ hsd hpd hh hbv
  have htwof := (certifiedTwoSum?_success_iff_finite_stages I s (twoProduct I a b).value.1).mp htwo
  have hσr := (twoSum_exact_of_range I s (twoProduct I a b).value.1 _ _ hsd hpd hh hbv).2
  have hσ := wordRat_cast_of_decode I _ _ hσr
  have hσd : (Datum.decode I (twoSum I s (twoProduct I a b).value.1).value.2).toRat? =
      some (wordRat I (twoSum I s (twoProduct I a b).value.1).value.2) := by
    have he := Datum.toRat?_decode I (twoSum I s (twoProduct I a b).value.1).value.2
    rw [hσr] at he
    obtain ⟨q,hq,_⟩ := Option.map_eq_some_iff.mp he
    simpa only [wordRat_of_decode I _ q hq] using hq
  simp only [twoProduct,mul] at hσ
  have htf := binary_even_finite_of_real_range I .add (twoProduct I a b).value.2
    (twoSum I s (twoProduct I a b).value.1).value.2 _ _ hπd hσd
    (by simpa [binaryExact,hσ,twoProduct,mul] using ht)
  have htd := finite_toRat_wordRat I _ htf
  have htr := binary_even_roundFinite_of_decode I .add (twoProduct I a b).value.2
    (twoSum I s (twoProduct I a b).value.1).value.2 _ _ _ hπd hσd htd
  simp only [twoProduct,mul,binaryExact,Rat.cast_add] at htr
  have hdf := binary_even_finite_of_real_range I .add c (dotStepTrace I s c a b).combined.value
    _ _ hcd htd (by simpa [binaryExact,htr,hσ,twoProduct,mul] using hd)
  exact ⟨hs,hc,ha,hb,hpf,htwof.2.2.1,htwof.2.2.2,htf,hdf⟩

theorem CompensatedDotPassRange.toFinite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotPassRange I a b n) : CompensatedDotPassFinite I a b n := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih h.1,CompensatedDotStepRange.toFinite I _ _ _ _ h.2⟩

theorem CompensatedDotRange.toFinite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotRange I a b n) : CompensatedDotFinite I a b n := by
  have hp := CompensatedDotPassRange.toFinite I a b n h.1
  have hf := CompensatedDotPassFinite.result_finite I a b n hp
  refine ⟨hp,?_⟩
  exact binary_even_finite_of_real_range I .add _ _ _ _
    (finite_toRat_wordRat I _ hf.1) (finite_toRat_wordRat I _ hf.2) (by simpa [binaryExact] using h.2)

theorem compensatedDot?_complete_of_range (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotRange I a b n) : ∃ r, compensatedDot? I a b n = some r :=
  compensatedDot?_complete I a b n (CompensatedDotRange.toFinite I a b n h)

theorem compensatedDot_mixed_of_range (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotRange I a b n) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*(geomWeight I.format.unitRoundoff (2*n)+n))+
            I.format.minSubnormal/2 :=
  compensatedDot_mixed_of_finite I a b n (CompensatedDotRange.toFinite I a b n h)

theorem compensatedDot_gamma_of_range (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotRange I a b n) (hn : (2*n : ℕ)*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          3*n*(I.format.minSubnormal/2)/(1-(2*n : ℕ)*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 :=
  compensatedDot_gamma_of_finite I a b n (CompensatedDotRange.toFinite I a b n h) hn

/-- Static exact-product conditions eliminate the measured product defects. -/
theorem twoProduct_defect_zero_of_range (I : Interchange) [I.Valid] (a b : I.Word)
    (h : TwoProductRange I a b) :
    wordRat I a*wordRat I b-wordRat I (twoProduct I a b).value.1-wordRat I (twoProduct I a b).value.2 = 0 := by
  obtain ⟨p,e,hp,he,hex⟩ := certifiedTwoProduct?_sound I a b _ _
    (finite_toRat_wordRat I a h.1) (finite_toRat_wordRat I b h.2.1) _ (certifiedTwoProduct?_of_range I a b h)
  have hpr := wordRat_cast_of_decode I _ p hp
  have her := wordRat_cast_of_decode I _ e he
  have hz : ((wordRat I a*wordRat I b-wordRat I (twoProduct I a b).value.1-
      wordRat I (twoProduct I a b).value.2 : ℚ) : ℝ) = 0 := by
    push_cast
    rw [hpr,her]
    linarith
  exact_mod_cast hz

theorem compensatedDotPass?_defect_zero (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (he : ∀ i < n, TwoProductRange I (a i) (b i))
    (r : Result (DotCompensationState I)) (hr : compensatedDotPass? I a b n = some r) :
    r.value.productDefectMass = 0 := by
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
        have heq : (⟨t.value,p.flags.union t.flags⟩ : Result (DotCompensationState I)) = r := by simpa [hp,ht] using hr
        cases heq
        have hz := ih (fun i hi => he i (by omega)) p hp
        have hv := twoProduct_defect_zero_of_range I (a n) (b n) (he n (by omega))
        unfold compensatedDotStep? at ht
        split_ifs at ht
        cases Option.some.inj ht
        simpa [dotCompensationUpdate,dotStepTrace,hz] using hv

theorem compensatedDot?_defect_zero (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (he : ∀ i < n, TwoProductRange I (a i) (b i))
    (r : CompensatedDotCertificate I) (hr : compensatedDot? I a b n = some r) : r.state.productDefectMass = 0 := by
  unfold compensatedDot? at hr
  cases hp : compensatedDotPass? I a b n with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    exact compensatedDotPass?_defect_zero I a b n he p hp

theorem compensatedDot_exact_products_bound (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (he : ∀ i < n, TwoProductRange I (a i) (b i)) (h : CompensatedDotFinite I a b n) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          (1+growth I.format.unitRoundoff (2*n))*((I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff (2*n)))+
            I.format.minSubnormal/2 := by
  obtain ⟨r,hr⟩ := compensatedDot?_complete I a b n h
  obtain ⟨q,hq,_,hb,_⟩ := compensatedDot?_sound I a b n r hr
  have hz := compensatedDot?_defect_zero I a b n he r hr
  refine ⟨q,?_,by simpa [hz] using hb⟩
  rw [compensatedDot?_execution I a b n r hr]
  exact hq

end FP.IEEE.Software
