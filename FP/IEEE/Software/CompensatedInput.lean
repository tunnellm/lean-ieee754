import FP.IEEE.Software.CompensatedCompleteness
import FP.CompensationInput

/-! Second-order IEEE compensated-summation bounds from the input magnitudes. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Sum of exact input magnitudes; its numerical interpretation uses finite inputs. -/
def wordListAbsSum (I : Interchange) (xs : List I.Word) : ℚ :=
  (xs.map (fun a => |wordRat I a|)).sum

theorem wordListAbsSum_nonneg (I : Interchange) (xs : List I.Word) : 0 ≤ wordListAbsSum I xs := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem wordListAbsSum_cast (I : Interchange) [I.Valid] (xs : List I.Word) (ys : List ℝ)
    (h : List.Forall₂ (fun w y => I.decode? w = some y) xs ys) :
    (wordListAbsSum I xs : ℝ) = (ys.map (fun y => |y|)).sum := by
  induction h with
  | nil => simp [wordListAbsSum]
  | @cons a y xs ys ha ht ih =>
    have hd := Datum.toRat?_decode I a
    rw [ha] at hd
    obtain ⟨q,hq,hqy⟩ := Option.map_eq_some_iff.mp hd
    have hw : (wordRat I a : ℝ) = y := by rw [wordRat_of_decode I _ q hq]; exact hqy
    simpa [wordListAbsSum,hw] using congrArg (fun z : ℝ => |y|+z) ih

/-- Additional invariants; the existing state and accounting structure stay unchanged. -/
def CompensationState.InputBound (I : Interchange) (st : CompensationState I)
    (T A : ℝ) (n : ℕ) : Prop :=
  |T| ≤ A ∧ |(wordRat I st.high : ℝ)-T| ≤ (st.residualMass : ℝ) ∧
  (st.residualMass : ℝ) ≤ growth I.format.unitRoundoff n*A+
    (I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff n

theorem compensation_initial_input_bound (I : Interchange) [I.Valid] :
    (CompensationState.initial I).InputBound I 0 0 0 := by
  simp [CompensationState.InputBound,CompensationState.initial,wordRat,Datum.fields,
    Fields.rationalValue,growth]

theorem compensatedStep?_input_bound (I : Interchange) [I.Valid] (st : CompensationState I)
    (a : I.Word) (T A : ℝ) (n : ℕ) (h : st.InputBound I T A n)
    (r : Result (CompensationState I)) (hr : compensatedStep? I st a = some r) :
    r.value.InputBound I (T+(wordRat I a : ℝ)) (A+|(wordRat I a : ℝ)|) (n+1) := by
  unfold compensatedStep? at hr
  cases ht : certifiedTwoSum? I st.high a with
  | none => simp [ht] at hr
  | some t =>
    rw [ht] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    obtain ⟨x,y,s,e,hx,hy,hs,he,hxy⟩ := certifiedTwoSum?_sound I st.high a t ht
    have wx := wordRat_of_decode I _ x hx
    have wy := wordRat_of_decode I _ y hy
    have ws := wordRat_of_decode I _ s hs
    have we := wordRat_of_decode I _ e he
    have htr := certifiedTwoSum?_execution I st.high a t ht
    have hsum : (Datum.decode I (add I .nearestEven st.high a).value).toRat? = some s := by
      simpa only [htr,twoSum,TwoSumTrace.result,twoSumTrace] using hs
    have herr := binary_even_error_of_decode I .add st.high a x y s hx hy hsum
    rcases h with ⟨hT,hh,hM⟩
    rw [wx] at hh
    have hn := FP.compensation_input_mass_step (a := (y : ℝ)) (s' := (s : ℝ)) (e := (e : ℝ))
      I.format.unitRoundoff_pos.le hT hh hM (by exact_mod_cast hxy)
      (by simpa [MixedError,binaryExact] using herr)
    simpa only [CompensationState.InputBound,compensationUpdate,wy,ws,we,
      Rat.cast_add,Rat.cast_abs] using hn

theorem compensatedAux?_input_bound (I : Interchange) [I.Valid] (xs : List I.Word)
    (st : CompensationState I) (T A : ℝ) (n : ℕ) (h : st.InputBound I T A n)
    (r : Result (CompensationState I)) (hr : compensatedAux? I st xs = some r) :
    r.value.InputBound I (T+(wordListSum I xs : ℝ)) (A+(wordListAbsSum I xs : ℝ)) (n+xs.length) := by
  induction xs generalizing st T A n r with
  | nil =>
    cases Option.some.inj hr
    simpa [wordListSum,wordListAbsSum,Result.pure] using h
  | cons a xs ih =>
    unfold compensatedAux? at hr
    cases ht : compensatedStep? I st a with
    | none => simp [ht] at hr
    | some t =>
      cases hout : compensatedAux? I t.value xs with
      | none => simp [ht,hout] at hr
      | some out =>
        have heq : (⟨out.value,Flags.union t.flags out.flags⟩ : Result (CompensationState I)) = r := by
          simpa [ht,hout] using hr
        cases heq
        have hn := ih t.value (T+(wordRat I a : ℝ)) (A+|(wordRat I a : ℝ)|) (n+1)
          (compensatedStep?_input_bound I st a T A n h t ht) out hout
        simpa [wordListSum,wordListAbsSum,add_assoc,Nat.add_comm,Nat.add_left_comm] using hn

theorem compensatedPass?_input_bound (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : Result (CompensationState I)) (hr : compensatedPass? I xs = some r) :
    r.value.InputBound I (wordListSum I xs : ℝ) (wordListAbsSum I xs : ℝ) xs.length := by
  simpa using compensatedAux?_input_bound I xs _ 0 0 0 (compensation_initial_input_bound I) r hr

/-- Recovered low parts have mass bounded by input magnitudes, even through underflow. -/
theorem compensatedSum?_residual_mass_bound (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : CompensatedCertificate I) (hr : compensatedSum? I xs = some r) :
    (r.state.residualMass : ℝ) ≤ growth I.format.unitRoundoff xs.length*(wordListAbsSum I xs : ℝ)+
      (I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff xs.length := by
  unfold compensatedSum? at hr
  cases hp : compensatedPass? I xs with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    exact (compensatedPass?_input_bound I xs p hp).2.2

/-- General input-based error bound for the total IEEE computation. Finiteness
is the only execution hypothesis; reconstruction and certificate success follow. -/
theorem compensatedSum_mixed_of_finite (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumFinite I xs) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff xs.length)^2*(wordListAbsSum I xs : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff xs.length)*
            geomWeight I.format.unitRoundoff xs.length)+I.format.minSubnormal/2 := by
  obtain ⟨r,hr⟩ := compensatedSum?_complete I xs h
  obtain ⟨q,hq,_,he,_⟩ := compensatedSum?_sound I xs r hr
  have hm := compensatedSum?_residual_mass_bound I xs r hr
  have hb := FP.compensation_input_bound I.format.unitRoundoff_pos.le hm he
  exact ⟨q,by rw [compensatedSum?_execution I xs r hr]; exact hq,hb⟩

theorem compensatedSum_gamma_of_finite (I : Interchange) [I.Valid] (xs : List I.Word)
    (h : CompensatedSumFinite I xs) (hn : xs.length*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff xs.length)^2*(wordListAbsSum I xs : ℝ)+
          xs.length*(I.format.minSubnormal/2)/(1-xs.length*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 := by
  obtain ⟨q,hq,he⟩ := compensatedSum_mixed_of_finite I xs h
  have hA : 0 ≤ (wordListAbsSum I xs : ℝ) := by exact_mod_cast wordListAbsSum_nonneg I xs
  have hε : 0 ≤ I.format.minSubnormal/2 := by unfold Format.minSubnormal; positivity
  exact ⟨q,hq,FP.compensation_input_gamma_bound I.format.unitRoundoff_pos hε hA hn he⟩

/-- A real-list interface makes both the target sum and input mass explicit. -/
theorem compensatedSum_mixed_of_decoded (I : Interchange) [I.Valid] (xs : List I.Word) (ys : List ℝ)
    (hdec : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (h : CompensatedSumFinite I xs) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-ys.sum| ≤ I.format.unitRoundoff*|ys.sum|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff ys.length)^2*(ys.map (fun y => |y|)).sum+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff ys.length)*
            geomWeight I.format.unitRoundoff ys.length)+I.format.minSubnormal/2 := by
  have he := compensatedSum_mixed_of_finite I xs h
  rw [wordListSum_cast I xs ys hdec,wordListAbsSum_cast I xs ys hdec,hdec.length_eq] at he
  exact he

theorem compensatedSum_gamma_of_decoded (I : Interchange) [I.Valid] (xs : List I.Word) (ys : List ℝ)
    (hdec : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (h : CompensatedSumFinite I xs) (hn : ys.length*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-ys.sum| ≤ I.format.unitRoundoff*|ys.sum|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff ys.length)^2*(ys.map (fun y => |y|)).sum+
          ys.length*(I.format.minSubnormal/2)/(1-ys.length*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 := by
  have he := compensatedSum_gamma_of_finite I xs h (by simpa [hdec.length_eq] using hn)
  rw [wordListSum_cast I xs ys hdec,wordListAbsSum_cast I xs ys hdec,hdec.length_eq] at he
  exact he

end FP.IEEE.Software
