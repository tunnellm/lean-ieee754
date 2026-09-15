import FP.IEEE.Software.CompensatedDotCompleteness

/-! End-to-end Dot2 bounds, backward interpretations, and certified enclosures. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange
open scoped BigOperators

theorem wordRat_cast_of_decode (I : Interchange) [I.Valid] (a : I.Word) (x : ℝ)
    (ha : I.decode? a = some x) : (wordRat I a : ℝ) = x := by
  have hd := Datum.toRat?_decode I a
  rw [ha] at hd
  obtain ⟨q,hq,hx⟩ := Option.map_eq_some_iff.mp hd
  rw [wordRat_of_decode I a q hq]
  exact hx

theorem wordDotSum_cast (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i)) :
    (wordDotSum I a b n : ℝ) = ∑ i ∈ Finset.range n, x i*y i := by
  unfold wordDotSum
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [wordRat_cast_of_decode I (a i) (x i) (ha i (Finset.mem_range.mp hi)),
    wordRat_cast_of_decode I (b i) (y i) (hb i (Finset.mem_range.mp hi))]

theorem wordDotAbsSum_cast (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i)) :
    (wordDotAbsSum I a b n : ℝ) = FP.dotMass x y n := by
  unfold wordDotAbsSum FP.dotMass
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [wordRat_cast_of_decode I (a i) (x i) (ha i (Finset.mem_range.mp hi)),
    wordRat_cast_of_decode I (b i) (y i) (hb i (Finset.mem_range.mp hi))]

/-- The certificate radius, the measured-defect bound, and the input-only bound
all describe the actual same result word. -/
theorem compensatedDot?_sound (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (r : CompensatedDotCertificate I) (hr : compensatedDot? I a b n = some r) :
    ∃ q : ℝ, I.decode? r.result.value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ (r.errorBound : ℝ) ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          (1+growth I.format.unitRoundoff (2*n))*((I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff (2*n)+
            (r.state.productDefectMass : ℝ)))+I.format.minSubnormal/2 ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*(geomWeight I.format.unitRoundoff (2*n)+n))+
            I.format.minSubnormal/2 := by
  unfold compensatedDot? at hr
  cases hp : compensatedDotPass? I a b n with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr with hf
    cases Option.some.inj hr
    have hv := compensatedDotPass?_valid I a b n p hp
    have hq := finite_toRat_wordRat I _ hf
    have herr := binary_even_error_of_decode I .add p.value.high p.value.correction _ _ _
      hv.high_finite hv.correction_finite hq
    have herrR : MixedError I.format.unitRoundoff (I.format.minSubnormal/2)
        ((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ))
        (wordRat I (add I .nearestEven p.value.high p.value.correction).value : ℝ) := by
      simpa [MixedError,binaryExact] using herr
    refine ⟨_,?_,?_,FP.dot_compensation_defect_bound I.format.unitRoundoff_pos.le hv.accounting herrR,
      FP.dot_compensation_input_bound I.format.unitRoundoff_pos.le hv.accounting herrR⟩
    · change I.decode? (add I .nearestEven p.value.high p.value.correction).value = _
      rw [← Datum.toRat?_decode,hq]; rfl
    · have ht := abs_add_le
        ((wordRat I (add I .nearestEven p.value.high p.value.correction).value : ℝ)-
          ((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ)))
        (((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ))-(wordDotSum I a b n : ℝ))
      rw [sub_add_sub_cancel] at ht
      simp only [Rat.cast_add,Rat.cast_abs,Rat.cast_sub]
      linarith [hv.accounting.error]

theorem compensatedDot_mixed_of_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotFinite I a b n) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*(geomWeight I.format.unitRoundoff (2*n)+n))+
            I.format.minSubnormal/2 := by
  obtain ⟨r,hr⟩ := compensatedDot?_complete I a b n h
  obtain ⟨q,hq,_,_,he⟩ := compensatedDot?_sound I a b n r hr
  exact ⟨q,by rw [compensatedDot?_execution I a b n r hr]; exact hq,he⟩

theorem compensatedDot_gamma_of_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotFinite I a b n) (hn : (2*n : ℕ)*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-(wordDotSum I a b n : ℝ)| ≤ I.format.unitRoundoff*|(wordDotSum I a b n : ℝ)|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff (2*n))^2*(wordDotAbsSum I a b n : ℝ)+
          3*n*(I.format.minSubnormal/2)/(1-(2*n : ℕ)*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 := by
  obtain ⟨q,hq,he⟩ := compensatedDot_mixed_of_finite I a b n h
  have hA : 0 ≤ (wordDotAbsSum I a b n : ℝ) := by unfold wordDotAbsSum; positivity
  have hε : 0 ≤ I.format.minSubnormal/2 := by unfold Format.minSubnormal; positivity
  exact ⟨q,hq,FP.dot_compensation_gamma_bound I.format.unitRoundoff_pos hε hA hn he⟩

theorem compensatedDot_mixed_of_decoded (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (h : CompensatedDotFinite I a b n) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ I.format.unitRoundoff*|∑ i ∈ Finset.range n, x i*y i|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*FP.dotMass x y n+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*(geomWeight I.format.unitRoundoff (2*n)+n))+
            I.format.minSubnormal/2 := by
  simpa only [wordDotSum_cast I a b x y n ha hb,wordDotAbsSum_cast I a b x y n ha hb]
    using compensatedDot_mixed_of_finite I a b n h

theorem compensatedDot_gamma_of_decoded (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (h : CompensatedDotFinite I a b n) (hn : (2*n : ℕ)*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ I.format.unitRoundoff*|∑ i ∈ Finset.range n, x i*y i|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff (2*n))^2*FP.dotMass x y n+
          3*n*(I.format.minSubnormal/2)/(1-(2*n : ℕ)*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 := by
  simpa only [wordDotSum_cast I a b x y n ha hb,wordDotAbsSum_cast I a b x y n ha hb]
    using compensatedDot_gamma_of_finite I a b n h hn

theorem compensatedDot_mixed_backward (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (h : CompensatedDotFinite I a b n) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      FP.MixedBackwardStable (I.format.unitRoundoff+(1+I.format.unitRoundoff)*(growth I.format.unitRoundoff (2*n))^2)
        ((1+I.format.unitRoundoff)*(I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*
          (geomWeight I.format.unitRoundoff (2*n)+n)+I.format.minSubnormal/2) x y n q := by
  obtain ⟨q,hq,he⟩ := compensatedDot_mixed_of_decoded I a b x y n ha hb h
  have hu := I.format.unitRoundoff_pos.le
  have hg := growth_nonneg hu (2*n)
  have hG := geomWeight_nonneg hu (2*n)
  have hε : 0 ≤ I.format.minSubnormal/2 := by unfold Format.minSubnormal; positivity
  refine ⟨q,hq,FP.mixedBackwardStable_of_abs (by positivity) (by positivity) x y n q ?_⟩
  have hS : |∑ i ∈ Finset.range n, x i*y i| ≤ FP.dotMass x y n := Finset.abs_sum_le_sum_abs _ _
  have hh := mul_le_mul_of_nonneg_left hS hu
  nlinarith

theorem compensatedDot_error_radius_of_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotFinite I a b n) :
    ∃ r, compensatedDot? I a b n = some r ∧ compensatedDot I a b n = r.result ∧
      ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
        |q-(wordDotSum I a b n : ℝ)| ≤ (r.errorBound : ℝ) := by
  obtain ⟨r,hr⟩ := compensatedDot?_complete I a b n h
  obtain ⟨q,hq,he,_⟩ := compensatedDot?_sound I a b n r hr
  exact ⟨r,hr,compensatedDot?_execution I a b n r hr,q,
    by rw [compensatedDot?_execution I a b n r hr]; exact hq,he⟩

theorem compensatedDot_exact_of_zero_bound (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : (compensatedDot? I a b n).map (fun r => r.errorBound) = some 0) :
    I.decode? (compensatedDot I a b n).value = some (wordDotSum I a b n : ℝ) := by
  cases hr : compensatedDot? I a b n with
  | none => simp [hr] at h
  | some r =>
    have hz : r.errorBound = 0 := by simpa [hr] using h
    obtain ⟨q,hq,he,_⟩ := compensatedDot?_sound I a b n r hr
    rw [hz,Rat.cast_zero] at he
    have heq : q = (wordDotSum I a b n : ℝ) := by simpa only [abs_nonpos_iff,sub_eq_zero] using he
    rw [compensatedDot?_execution I a b n r hr]
    simpa [heq] using hq

def compensatedDotEnclosure? (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ) : Option FP.Range.Interval := do
  let r ← compensatedDot? I a b n
  some ⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩

theorem compensatedDotEnclosure?_sound (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (J : FP.Range.Interval) (hJ : compensatedDotEnclosure? I a b n = some J) :
    J.Contains (wordDotSum I a b n : ℝ) := by
  unfold compensatedDotEnclosure? at hJ
  cases hr : compensatedDot? I a b n with
  | none => simp [hr] at hJ
  | some r =>
    have heq : (⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩ : FP.Range.Interval) = J := by
      simpa [hr] using hJ
    cases heq
    obtain ⟨q,hq,he,_⟩ := compensatedDot?_sound I a b n r hr
    have hw := wordRat_cast_of_decode I r.result.value q hq
    simp only [FP.Range.Interval.Contains,Rat.cast_sub,Rat.cast_add,hw]
    constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2]

theorem compensatedDotEnclosure?_exists_of_finite (I : Interchange) [I.Valid] (a b : ℕ → I.Word) (n : ℕ)
    (h : CompensatedDotFinite I a b n) :
    ∃ J, compensatedDotEnclosure? I a b n = some J ∧ J.Contains (wordDotSum I a b n : ℝ) := by
  obtain ⟨r,hr⟩ := compensatedDot?_complete I a b n h
  let J : FP.Range.Interval := ⟨wordRat I r.result.value-r.errorBound,wordRat I r.result.value+r.errorBound⟩
  have hJ : compensatedDotEnclosure? I a b n = some J := by simp [compensatedDotEnclosure?,hr,J]
  exact ⟨J,hJ,compensatedDotEnclosure?_sound I a b n J hJ⟩

end FP.IEEE.Software
