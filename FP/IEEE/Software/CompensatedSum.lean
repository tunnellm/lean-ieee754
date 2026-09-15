import FP.IEEE.Software.TwoSum
import FP.Compensation

/-! Online compensated summation using certified classical TwoSum steps.
The certificate accounts for correction-addition errors rather than requiring
those additions to be exact. Summation operations use IEEE words; a rational
sidecar accounts for their errors. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

structure CompensationState (I : Interchange) where
  high : I.Word
  correction : I.Word
  radius : ℚ
  residualMass : ℚ
  highMass : ℚ

def CompensationState.initial (I : Interchange) : CompensationState I :=
  ⟨(Datum.zero false).encode,(Datum.zero false).encode,0,0,0⟩

def compensationUpdate (I : Interchange) (st : CompensationState I) (a : I.Word)
    (t : Result (I.Word × I.Word)) (c : Result I.Word) : CompensationState I :=
  ⟨t.value.1,c.value,
    st.radius + |wordRat I c.value - (wordRat I st.correction + wordRat I t.value.2)|,
    st.residualMass + |wordRat I t.value.2|,
    st.highMass + |wordRat I st.high + wordRat I a|⟩

def compensatedStep? (I : Interchange) [I.Valid] (st : CompensationState I) (a : I.Word) :
    Option (Result (CompensationState I)) :=
  match certifiedTwoSum? I st.high a with
  | none => none
  | some t =>
    let c := add I .nearestEven st.correction t.value.2
    if (Datum.decode I st.correction).isFinite && (Datum.decode I c.value).isFinite then
      some ⟨compensationUpdate I st a t c, Flags.union t.flags c.flags⟩
    else none

def compensatedAux? (I : Interchange) [I.Valid] (st : CompensationState I) :
    List I.Word → Option (Result (CompensationState I))
  | [] => some (Result.pure st)
  | a::xs => do
    let t ← compensatedStep? I st a
    let r ← compensatedAux? I t.value xs
    some ⟨r.value,Flags.union t.flags r.flags⟩

def compensatedPass? (I : Interchange) [I.Valid] (xs : List I.Word) : Option (Result (CompensationState I)) :=
  compensatedAux? I (CompensationState.initial I) xs

/-- Real invariant attached to the executable state. -/
structure CompensationState.Valid (I : Interchange) (st : CompensationState I) (total : ℝ) (n : ℕ) : Prop where
  high_finite : (Datum.decode I st.high).toRat? = some (wordRat I st.high)
  correction_finite : (Datum.decode I st.correction).toRat? = some (wordRat I st.correction)
  accounting : FP.CompensationInvariant I.format.unitRoundoff (I.format.minSubnormal/2) total
    (wordRat I st.high) (wordRat I st.correction) st.radius st.residualMass st.highMass n

theorem compensation_initial_valid (I : Interchange) [I.Valid] :
    (CompensationState.initial I).Valid I 0 0 := by
  have hz : wordRat I (Datum.zero false).encode = 0 := by simp [wordRat, Datum.fields, Fields.rationalValue]
  constructor
  · simp [CompensationState.initial, hz]
  · simp [CompensationState.initial, hz]
  · simpa [CompensationState.initial, hz] using FP.compensation_zero I.format.unitRoundoff (I.format.minSubnormal/2)

theorem compensatedStep?_valid (I : Interchange) [I.Valid] (st : CompensationState I) (a : I.Word)
    (total : ℝ) (n : ℕ) (hv : st.Valid I total n) (r : Result (CompensationState I))
    (hr : compensatedStep? I st a = some r) : r.value.Valid I (total+(wordRat I a : ℝ)) (n+1) := by
  unfold compensatedStep? at hr
  cases ht : certifiedTwoSum? I st.high a with
  | none => simp [ht] at hr
  | some t =>
    rw [ht] at hr
    dsimp only at hr
    split_ifs at hr with hf
    cases Option.some.inj hr
    have hcf : (Datum.decode I (add I .nearestEven st.correction t.value.2).value).isFinite = true := by
      have hboth : (Datum.decode I st.correction).isFinite = true ∧
          (Datum.decode I (add I .nearestEven st.correction t.value.2).value).isFinite = true := by simpa using hf
      exact hboth.2
    obtain ⟨x,y,s,e,hx,hy,hs,he,hxy⟩ := certifiedTwoSum?_sound I st.high a t ht
    obtain ⟨c,hc⟩ := finite_decode_exists I _ hcf
    have wx := wordRat_of_decode I _ x hx
    have wy := wordRat_of_decode I _ y hy
    have ws := wordRat_of_decode I _ s hs
    have we := wordRat_of_decode I _ e he
    have wc := wordRat_of_decode I _ c hc
    have hsum : (Datum.decode I (add I .nearestEven st.high a).value).toRat? = some s := by
      have htr : t = twoSum I st.high a := by
        unfold certifiedTwoSum? at ht
        dsimp only at ht
        split_ifs at ht
        exact (Option.some.inj ht).symm
      simpa only [htr, twoSum, TwoSumTrace.result, twoSumTrace] using hs
    have highErr := binary_even_error_of_decode I .add st.high a x y s hx hy hsum
    have corrErr := binary_even_error_of_decode I .add st.correction t.value.2
      (wordRat I st.correction) e c hv.correction_finite he hc
    constructor
    · simpa only [compensationUpdate, ws] using hs
    · simpa only [compensationUpdate, wc] using hc
    · have h0 := hv.accounting
      rw [wx] at h0
      have hε : 0 ≤ I.format.minSubnormal/2 := by unfold Format.minSubnormal; positivity
      have step := FP.compensation_step (a := (y : ℝ)) (s' := (s : ℝ)) (e := (e : ℝ)) (c' := (c : ℝ))
        I.format.unitRoundoff_pos.le hε h0 (by exact_mod_cast hxy)
        (by simpa [MixedError, binaryExact, Rat.cast_add] using highErr)
        (by simpa [MixedError, binaryExact, Rat.cast_add] using corrErr)
      simpa only [compensationUpdate, wx, wy, ws, we, wc, Rat.cast_add, Rat.cast_sub, Rat.cast_abs] using step

/-- Exact values of the inputs; a successful pass has checked every used operand. -/
def wordListSum (I : Interchange) (xs : List I.Word) : ℚ := (xs.map (wordRat I)).sum

theorem compensatedAux?_valid (I : Interchange) [I.Valid] (xs : List I.Word)
    (st : CompensationState I) (total : ℝ) (n : ℕ) (hv : st.Valid I total n)
    (r : Result (CompensationState I)) (hr : compensatedAux? I st xs = some r) :
    r.value.Valid I (total+(wordListSum I xs : ℝ)) (n+xs.length) := by
  induction xs generalizing st total n r with
  | nil =>
    have heq : Result.pure st = r := Option.some.inj hr
    cases heq
    simpa [wordListSum, Result.pure] using hv
  | cons a xs ih =>
    unfold compensatedAux? at hr
    cases ht : compensatedStep? I st a with
    | none => simp [ht] at hr
    | some t =>
      cases hout : compensatedAux? I t.value xs with
      | none => simp [ht, hout] at hr
      | some out =>
        have heq : (⟨out.value,Flags.union t.flags out.flags⟩ : Result (CompensationState I)) = r := by
          simpa [ht,hout] using hr
        cases heq
        have h := ih t.value (total+(wordRat I a : ℝ)) (n+1)
          (compensatedStep?_valid I st a total n hv t ht) out hout
        simpa [wordListSum, add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem compensatedPass?_valid (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : Result (CompensationState I)) (hr : compensatedPass? I xs = some r) :
    r.value.Valid I (wordListSum I xs : ℝ) xs.length := by
  simpa using compensatedAux?_valid I xs _ 0 0 (compensation_initial_valid I) r hr

structure CompensatedCertificate (I : Interchange) where
  result : Result I.Word
  state : CompensationState I
  errorBound : ℚ

/-- Finish the compensated pass with one final nearest-even addition. The returned
rational radius encloses all correction errors and the final rounding error. -/
def compensatedSum? (I : Interchange) [I.Valid] (xs : List I.Word) : Option (CompensatedCertificate I) :=
  match compensatedPass? I xs with
  | none => none
  | some p =>
    let r := add I .nearestEven p.value.high p.value.correction
    if (Datum.decode I r.value).isFinite then
      some ⟨⟨r.value,Flags.union p.flags r.flags⟩,p.value,
        p.value.radius + |wordRat I r.value - (wordRat I p.value.high + wordRat I p.value.correction)|⟩
    else none

/-- End-to-end bounds for the actual decoded result. The first bound is executable;
the next two explain the residual-mass and second-order structure of the error. -/
theorem compensatedSum?_sound (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : CompensatedCertificate I) (hr : compensatedSum? I xs = some r) :
    ∃ q : ℝ, I.decode? r.result.value = some q ∧
      |q-(wordListSum I xs : ℝ)| ≤ (r.errorBound : ℝ) ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)| +
        (1+I.format.unitRoundoff)*(growth I.format.unitRoundoff xs.length*(r.state.residualMass : ℝ) +
          (I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff xs.length) + I.format.minSubnormal/2 ∧
      |q-(wordListSum I xs : ℝ)| ≤ I.format.unitRoundoff*|(wordListSum I xs : ℝ)| +
        (1+I.format.unitRoundoff)*(growth I.format.unitRoundoff xs.length*
          (I.format.unitRoundoff*(r.state.highMass : ℝ)+xs.length*(I.format.minSubnormal/2)) +
          (I.format.minSubnormal/2)*geomWeight I.format.unitRoundoff xs.length) + I.format.minSubnormal/2 := by
  unfold compensatedSum? at hr
  cases hp : compensatedPass? I xs with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr with hf
    cases Option.some.inj hr
    have hv := compensatedPass?_valid I xs p hp
    obtain ⟨q,hq⟩ := finite_decode_exists I _ hf
    have wq := wordRat_of_decode I _ q hq
    have herr := binary_even_error_of_decode I .add p.value.high p.value.correction
      (wordRat I p.value.high) (wordRat I p.value.correction) q hv.high_finite hv.correction_finite hq
    have herrR : MixedError I.format.unitRoundoff (I.format.minSubnormal/2)
        ((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ)) (q : ℝ) := by
      simpa [MixedError,binaryExact,Rat.cast_add] using herr
    refine ⟨(q : ℝ), ?_, ?_,
      FP.compensation_residual_bound I.format.unitRoundoff_pos.le hv.accounting herrR,
      FP.compensation_second_order I.format.unitRoundoff_pos.le hv.accounting herrR⟩
    · change I.decode? (add I .nearestEven p.value.high p.value.correction).value = _
      rw [← Datum.toRat?_decode,hq]; rfl
    · have ht := abs_add_le
        ((q : ℝ)-((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ)))
        (((wordRat I p.value.high : ℝ)+(wordRat I p.value.correction : ℝ))-(wordListSum I xs : ℝ))
      rw [sub_add_sub_cancel] at ht
      simp only [wq,Rat.cast_add,Rat.cast_abs,Rat.cast_sub]
      linarith [hv.accounting.error]

/-- Exact sums of supplied decoded inputs agree with the certificate's target. -/
theorem wordListSum_cast (I : Interchange) [I.Valid] (xs : List I.Word) (ys : List ℝ)
    (h : List.Forall₂ (fun w y => I.decode? w = some y) xs ys) :
    (wordListSum I xs : ℝ) = ys.sum := by
  induction h with
  | nil => simp [wordListSum]
  | @cons a y xs ys ha ht ih =>
    have hd := Datum.toRat?_decode I a
    rw [ha] at hd
    obtain ⟨q,hq,hqy⟩ := Option.map_eq_some_iff.mp hd
    have hw : (wordRat I a : ℝ) = y := by rw [wordRat_of_decode I a q hq]; exact hqy
    simpa [wordListSum,hw] using congrArg (fun z : ℝ => y+z) ih

/-- Every input consumed by a successful pass was checked finite. -/
theorem compensatedAux?_finite_inputs (I : Interchange) [I.Valid] (xs : List I.Word)
    (st : CompensationState I) (r : Result (CompensationState I))
    (hr : compensatedAux? I st xs = some r) :
    ∀ a ∈ xs, (Datum.decode I a).isFinite = true := by
  induction xs generalizing st r with
  | nil => simp
  | cons a xs ih =>
    unfold compensatedAux? at hr
    cases ht : compensatedStep? I st a with
    | none => simp [ht] at hr
    | some t =>
      cases hout : compensatedAux? I t.value xs with
      | none => simp [ht,hout] at hr
      | some out =>
        have ha : (Datum.decode I a).isFinite = true := by
          unfold compensatedStep? at ht
          cases htwo : certifiedTwoSum? I st.high a with
          | none => simp [htwo] at ht
          | some two =>
            obtain ⟨x,y,s,e,hx,hy,hs,he,heq⟩ := certifiedTwoSum?_sound I st.high a two htwo
            rw [← Datum.toRat?_isSome,hy]; rfl
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact ih t.value out hout b hb

/-- The final certificate retains the pass flags and final-addition flags. -/
theorem compensatedSum?_flags (I : Interchange) [I.Valid] (xs : List I.Word)
    (r : CompensatedCertificate I) (hr : compensatedSum? I xs = some r) :
    ∃ p : Result (CompensationState I), compensatedPass? I xs = some p ∧
      r.result.flags = p.flags.union (add I .nearestEven p.value.high p.value.correction).flags := by
  unfold compensatedSum? at hr
  cases hp : compensatedPass? I xs with
  | none => simp [hp] at hr
  | some p =>
    rw [hp] at hr
    dsimp only at hr
    split_ifs at hr
    cases Option.some.inj hr
    exact ⟨p,rfl,rfl⟩
end FP.IEEE.Software
