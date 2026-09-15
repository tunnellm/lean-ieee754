import FP.IEEE.TwoSumExact
import FP.IEEE.Software.Cancellation

/-! General IEEE TwoSum exactness from finite inputs and the first two stages.
The remaining four stages are proved exact; runtime reconstruction certificates
are conclusions, not hypotheses. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Transfer the two general reconstruction lemmas to decoded IEEE words. -/
theorem twoSum_reconstructions_representable (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    I.format.Representable ((s-bv : ℚ) : ℝ) ∧
      I.format.Representable ((y-bv : ℚ) : ℝ) := by
  have hseq := binary_even_roundFinite_of_decode I .add a b x y s ha hb hs
  have hveq := binary_even_roundFinite_of_decode I .sub _ a s x bv hs ha hv
  simp only [binaryExact, Rat.cast_add, Rat.cast_sub] at hseq hveq
  simpa only [Rat.cast_sub] using I.format.twoSum_reconstructions
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb)
    (rat_representable_of_decode I _ s hs) (rat_representable_of_decode I _ bv hv) hseq hveq

/-- Certificate success follows from finiteness of the inputs and first two stages. -/
theorem certifiedTwoSum?_of_finite_stages (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  obtain ⟨hav,hbr⟩ := twoSum_reconstructions_representable I a b x y s bv ha hb hs hv
  exact certifiedTwoSum?_of_two_reconstructions I a b x y s bv ha hb hs hv hav hbr

/-- Classical TwoSum returns the rounded sum and its exact error as finite words. -/
theorem twoSum_exact_of_finite_stages (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    (Datum.decode I (twoSum I a b).value.1).toRat? = some s ∧
      (Datum.decode I (twoSum I a b).value.2).toRat? = some (x+y-s) := by
  have hc := certifiedTwoSum?_of_finite_stages I a b x y s bv ha hb hs hv
  obtain ⟨u,v,t,e,hu,hv',ht,he,h⟩ := certifiedTwoSum?_sound I a b _ hc
  have hux : u = x := Option.some.inj (hu.symm.trans ha)
  have hvy : v = y := Option.some.inj (hv'.symm.trans hb)
  have hts : t = s := Option.some.inj (ht.symm.trans hs)
  subst u v t
  have heq : e = x+y-s := by linarith
  exact ⟨hs,by simpa [heq] using he⟩

private theorem checked_of_success (I : Interchange) [I.Valid] (a b : I.Word)
    (hc : certifiedTwoSum? I a b = some (twoSum I a b)) :
    (twoSumTrace I a b).checked = true := by
  unfold certifiedTwoSum? at hc
  dsimp only at hc
  split_ifs at hc with hf
  have hh : (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
      (twoSumTrace I a b).checked = true := by simpa [and_assoc] using hf
  exact hh.2.2

/-- The four reconstruction operations raise no exceptions, including inexact. -/
theorem twoSum_reconstruction_flags_of_finite_stages (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    (twoSumTrace I a b).avirt.flags = Flags.empty ∧
    (twoSumTrace I a b).bround.flags = Flags.empty ∧
    (twoSumTrace I a b).around.flags = Flags.empty ∧
    (twoSumTrace I a b).error.flags = Flags.empty := by
  have hc := checked_of_success I a b (certifiedTwoSum?_of_finite_stages I a b x y s bv ha hb hs hv)
  have hh : (Datum.decode I (twoSumTrace I a b).sum.value).isFinite = true ∧
      (Datum.decode I (twoSumTrace I a b).bvirt.value).isFinite = true ∧
      flagsClear (twoSumTrace I a b).avirt.flags = true ∧
      flagsClear (twoSumTrace I a b).bround.flags = true ∧
      flagsClear (twoSumTrace I a b).around.flags = true ∧
      flagsClear (twoSumTrace I a b).error.flags = true := by
    simpa [TwoSumTrace.checked, and_assoc] using hc
  exact ⟨(flagsClear_iff _).mp hh.2.2.1, (flagsClear_iff _).mp hh.2.2.2.1,
    (flagsClear_iff _).mp hh.2.2.2.2.1, (flagsClear_iff _).mp hh.2.2.2.2.2⟩

/-- The actual decoded values at all four reconstruction stages are exact. -/
theorem twoSum_reconstruction_values_of_finite_stages (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    (Datum.decode I (twoSumTrace I a b).avirt.value).toRat? = some (s-bv) ∧
    (Datum.decode I (twoSumTrace I a b).bround.value).toRat? = some (y-bv) ∧
    (Datum.decode I (twoSumTrace I a b).around.value).toRat? = some (x-(s-bv)) ∧
    (Datum.decode I (twoSumTrace I a b).error.value).toRat? = some (x+y-s) := by
  obtain ⟨fav,fbr,far,_⟩ := twoSum_reconstruction_flags_of_finite_stages I a b x y s bv ha hb hs hv
  have hav := binary_exact_of_no_flags I .sub .nearestEven _ _ s bv hs hv fav
  have hbr := binary_exact_of_no_flags I .sub .nearestEven _ _ y bv hb hv fbr
  have har := binary_exact_of_no_flags I .sub .nearestEven _ _ x (s-bv) ha hav far
  exact ⟨hav,hbr,har,(twoSum_exact_of_finite_stages I a b x y s bv ha hb hs hv).2⟩

/-- Only the first two operations contribute sticky flags. They may be inexact. -/
theorem twoSum_flags_of_finite_stages (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv) :
    (twoSum I a b).flags =
      (twoSumTrace I a b).sum.flags.union (twoSumTrace I a b).bvirt.flags := by
  obtain ⟨hav,hbr,har,he⟩ := twoSum_reconstruction_flags_of_finite_stages I a b x y s bv ha hb hs hv
  change (twoSumTrace I a b).flags = _
  simp only [TwoSumTrace.flags, hav, hbr, har, he]
  funext f
  simp [Flags.union, Flags.empty]

/-- This precisely characterizes certificate success; all reconstruction checks
are redundant once the inputs and the first two stages are finite. -/
theorem certifiedTwoSum?_success_iff_finite_stages (I : Interchange) [I.Valid] (a b : I.Word) :
    certifiedTwoSum? I a b = some (twoSum I a b) ↔
      (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
      (Datum.decode I (twoSumTrace I a b).sum.value).isFinite = true ∧
      (Datum.decode I (twoSumTrace I a b).bvirt.value).isFinite = true := by
  constructor
  · intro hc
    unfold certifiedTwoSum? at hc
    dsimp only at hc
    split_ifs at hc with hf
    simp only [TwoSumTrace.checked, Bool.and_eq_true] at hf
    exact ⟨hf.1.1,hf.1.2,hf.2.1.1.1.1.1,hf.2.1.1.1.1.2⟩
  · rintro ⟨ha,hb,hs,hv⟩
    obtain ⟨x,hx⟩ := finite_decode_exists I a ha
    obtain ⟨y,hy⟩ := finite_decode_exists I b hb
    obtain ⟨s,hs⟩ := finite_decode_exists I _ hs
    obtain ⟨bv,hv⟩ := finite_decode_exists I _ hv
    exact certifiedTwoSum?_of_finite_stages I a b x y s bv hx hy hs hv

/-- Finite inputs and a finite first two stages suffice for a real exact split. -/
theorem twoSum_exact_of_finite (I : Interchange) [I.Valid] (a b : I.Word)
    (ha : (Datum.decode I a).isFinite = true) (hb : (Datum.decode I b).isFinite = true)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).isFinite = true)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).isFinite = true) :
    ∃ x y s e : ℚ, (Datum.decode I a).toRat? = some x ∧
      (Datum.decode I b).toRat? = some y ∧
      (Datum.decode I (twoSum I a b).value.1).toRat? = some s ∧
      (Datum.decode I (twoSum I a b).value.2).toRat? = some e ∧
      (x : ℝ)+(y : ℝ) = (s : ℝ)+(e : ℝ) := by
  obtain ⟨x,y,s,e,hx,hy,hs,he,heq⟩ := certifiedTwoSum?_sound I a b _
    ((certifiedTwoSum?_success_iff_finite_stages I a b).mpr ⟨ha,hb,hs,hv⟩)
  exact ⟨x,y,s,e,hx,hy,hs,he,by exact_mod_cast heq⟩

private theorem binary_even_finite_of_range (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hrange : |(binaryExact op x y : ℝ)| < I.format.overflowThreshold) :
    ∃ z : ℚ, (Datum.decode I (binary I op .nearestEven a b).value).toRat? = some z := by
  have hcast : |(binaryExact op x y : ℝ)| < (overflowThreshold I.format : ℝ) := by
    simpa using hrange
  have hq : |binaryExact op x y| < overflowThreshold I.format := by exact_mod_cast hcast
  exact ⟨scaledRound I.format .nearestEven (binaryExact op x y), by
    rw [binary_even_projection I op a b x y ha hb]
    simp [roundNearest?, hq]⟩

private theorem finite_stages_of_range (I : Interchange) [I.Valid]
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hsum : |(x : ℝ)+(y : ℝ)| < I.format.overflowThreshold)
    (hbvirt : |I.format.roundFinite ((x : ℝ)+(y : ℝ))-(x : ℝ)| < I.format.overflowThreshold) :
    ∃ s bv : ℚ, (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s ∧
      (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv := by
  obtain ⟨s,hs⟩ := binary_even_finite_of_range I .add a b x y ha hb
    (by simpa [binaryExact] using hsum)
  have hsr := binary_even_roundFinite_of_decode I .add a b x y s ha hb hs
  simp only [binaryExact, Rat.cast_add] at hsr
  obtain ⟨bv,hv⟩ := binary_even_finite_of_range I .sub _ a s x hs ha
    (by simpa [binaryExact, hsr] using hbvirt)
  exact ⟨s,bv,hs,hv⟩

/-- Explicit real range hypotheses imply success, including gradual underflow. -/
theorem certifiedTwoSum?_of_range (I : Interchange) [I.Valid]
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hsum : |(x : ℝ)+(y : ℝ)| < I.format.overflowThreshold)
    (hbvirt : |I.format.roundFinite ((x : ℝ)+(y : ℝ))-(x : ℝ)| < I.format.overflowThreshold) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  obtain ⟨s,bv,hs,hv⟩ := finite_stages_of_range I a b x y ha hb hsum hbvirt
  exact certifiedTwoSum?_of_finite_stages I a b x y s bv ha hb hs hv

/-- Real-valued IEEE TwoSum: the actual output words are the rounded sum and
its exact residual, under the two necessary operation-range qualifications. -/
theorem twoSum_exact_of_range (I : Interchange) [I.Valid]
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hsum : |(x : ℝ)+(y : ℝ)| < I.format.overflowThreshold)
    (hbvirt : |I.format.roundFinite ((x : ℝ)+(y : ℝ))-(x : ℝ)| < I.format.overflowThreshold) :
    I.decode? (twoSum I a b).value.1 = some (I.format.roundFinite ((x : ℝ)+(y : ℝ))) ∧
    I.decode? (twoSum I a b).value.2 =
      some ((x : ℝ)+(y : ℝ)-I.format.roundFinite ((x : ℝ)+(y : ℝ))) := by
  obtain ⟨s,bv,hs,hv⟩ := finite_stages_of_range I a b x y ha hb hsum hbvirt
  have hr := twoSum_exact_of_finite_stages I a b x y s bv ha hb hs hv
  have hsr := binary_even_roundFinite_of_decode I .add a b x y s ha hb hs
  simp only [binaryExact, Rat.cast_add] at hsr
  have hhigh := congrArg (Option.map (fun q : ℚ => (q : ℝ))) hr.1
  have hlow := congrArg (Option.map (fun q : ℚ => (q : ℝ))) hr.2
  rw [Datum.toRat?_decode] at hhigh hlow
  exact ⟨by simpa [hsr] using hhigh, by simpa [hsr] using hlow⟩

end FP.IEEE.Software
