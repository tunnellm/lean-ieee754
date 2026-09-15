import FP.IEEE.Software.ProductResidual
import FP.IEEE.Spec.TwoSum

/-! Classical six-operation TwoSum and a sufficient exactness certificate.
The rounded sum and virtual second addend may be inexact; the four reconstruction
operations must be exact for the certificate below. No operand-magnitude ordering
is required. All six operation-local flags are retained. The general proof that
finite inputs/sum/bvirt imply certificate success is in `Software/TwoSumExact`. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

structure TwoSumTrace (I : Interchange) where
  sum : Result I.Word
  bvirt : Result I.Word
  avirt : Result I.Word
  bround : Result I.Word
  around : Result I.Word
  error : Result I.Word

def twoSumTrace (I : Interchange) [I.Valid] (a b : I.Word) : TwoSumTrace I :=
  let s := add I .nearestEven a b
  let bv := sub I .nearestEven s.value a
  let av := sub I .nearestEven s.value bv.value
  let br := sub I .nearestEven b bv.value
  let ar := sub I .nearestEven a av.value
  let e := add I .nearestEven ar.value br.value
  ⟨s,bv,av,br,ar,e⟩

def TwoSumTrace.flags {I : Interchange} (t : TwoSumTrace I) : Flags :=
  t.sum.flags.union (t.bvirt.flags.union (t.avirt.flags.union
    (t.bround.flags.union (t.around.flags.union t.error.flags))))

def TwoSumTrace.result {I : Interchange} (t : TwoSumTrace I) : Result (I.Word × I.Word) :=
  ⟨(t.sum.value,t.error.value),t.flags⟩

def twoSum (I : Interchange) [I.Valid] (a b : I.Word) : Result (I.Word × I.Word) :=
  (twoSumTrace I a b).result

/-- These checks certify local exactness, not a comparison against the desired sum. -/
def TwoSumTrace.checked {I : Interchange} (t : TwoSumTrace I) : Bool :=
  (Datum.decode I t.sum.value).isFinite && (Datum.decode I t.bvirt.value).isFinite &&
    flagsClear t.avirt.flags && flagsClear t.bround.flags &&
    flagsClear t.around.flags && flagsClear t.error.flags

def certifiedTwoSum? (I : Interchange) [I.Valid] (a b : I.Word) : Option (Result (I.Word × I.Word)) :=
  let t := twoSumTrace I a b
  if (Datum.decode I a).isFinite && (Datum.decode I b).isFinite && t.checked then some t.result else none

/-- Reusable transfer of an exactness flag certificate to rational decoding. -/
theorem binary_exact_of_no_flags (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ) (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y) (hf : (binary I op mode a b).flags = Flags.empty) :
    (Datum.decode I (binary I op mode a b).value).toRat? = some (binaryExact op x y) := by
  rw [binary_finite I op mode a b x y ha hb] at hf ⊢
  have hr := roundWithMode_exact_of_no_flags I mode _ _ hf
  have h := (Datum.toRat?_decode I _).trans hr
  exact (Option.map_injective Rat.cast_injective) h

theorem finite_decode_exists (I : Interchange) (a : I.Word) (ha : (Datum.decode I a).isFinite = true) :
    ∃ x : ℚ, (Datum.decode I a).toRat? = some x := by
  exact ⟨(Datum.decode I a).fields.rationalValue, by simp [Datum.toRat?, ha]⟩

/-- An algebraic TwoSum proof from certified exact reconstruction operations. -/
theorem twoSum_checked_exact (I : Interchange) [I.Valid] (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hc : (twoSumTrace I a b).checked = true) :
    ∃ s e : ℚ, (Datum.decode I (twoSum I a b).value.1).toRat? = some s ∧
      (Datum.decode I (twoSum I a b).value.2).toRat? = some e ∧ x+y = s+e := by
  have hs : (Datum.decode I (twoSumTrace I a b).sum.value).isFinite = true ∧
      (Datum.decode I (twoSumTrace I a b).bvirt.value).isFinite = true ∧
      flagsClear (twoSumTrace I a b).avirt.flags = true ∧
      flagsClear (twoSumTrace I a b).bround.flags = true ∧
      flagsClear (twoSumTrace I a b).around.flags = true ∧
      flagsClear (twoSumTrace I a b).error.flags = true := by
    simpa [TwoSumTrace.checked, and_assoc] using hc
  obtain ⟨s, hsum⟩ := finite_decode_exists I _ hs.1
  obtain ⟨bv, hbv⟩ := finite_decode_exists I _ hs.2.1
  have hav := binary_exact_of_no_flags I .sub .nearestEven _ _ s bv hsum hbv
    ((flagsClear_iff _).mp hs.2.2.1)
  have hbr := binary_exact_of_no_flags I .sub .nearestEven _ _ y bv hb hbv
    ((flagsClear_iff _).mp hs.2.2.2.1)
  have har := binary_exact_of_no_flags I .sub .nearestEven _ _ x (s-bv) ha hav
    ((flagsClear_iff _).mp hs.2.2.2.2.1)
  have herr := binary_exact_of_no_flags I .add .nearestEven _ _ (x-(s-bv)) (y-bv) har hbr
    ((flagsClear_iff _).mp hs.2.2.2.2.2)
  exact ⟨s, (x-(s-bv))+(y-bv), hsum, herr, by ring⟩

theorem certifiedTwoSum?_sound (I : Interchange) [I.Valid] (a b : I.Word)
    (r : Result (I.Word × I.Word)) (hr : certifiedTwoSum? I a b = some r) :
    ∃ x y s e : ℚ, (Datum.decode I a).toRat? = some x ∧ (Datum.decode I b).toRat? = some y ∧
      (Datum.decode I r.value.1).toRat? = some s ∧ (Datum.decode I r.value.2).toRat? = some e ∧ x+y=s+e := by
  unfold certifiedTwoSum? at hr
  dsimp only at hr
  split_ifs at hr with hf
  cases Option.some.inj hr
  have h : (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
      (twoSumTrace I a b).checked = true := by simpa [and_assoc] using hf
  obtain ⟨x,hx⟩ := finite_decode_exists I a h.1
  obtain ⟨y,hy⟩ := finite_decode_exists I b h.2.1
  obtain ⟨s,e,hs,he,hxy⟩ := twoSum_checked_exact I a b x y hx hy h.2.2
  exact ⟨x,y,s,e,hx,hy,hs,he,hxy⟩

/-- Sticky flags account for all six executed operations, including inexact bvirt. -/
theorem twoSum_flags (I : Interchange) [I.Valid] (a b : I.Word) (f : Exception) :
    (twoSum I a b).flags f = true ↔
      (twoSumTrace I a b).sum.flags f = true ∨ (twoSumTrace I a b).bvirt.flags f = true ∨
      (twoSumTrace I a b).avirt.flags f = true ∨ (twoSumTrace I a b).bround.flags f = true ∨
      (twoSumTrace I a b).around.flags f = true ∨ (twoSumTrace I a b).error.flags f = true := by
  simp [twoSum, TwoSumTrace.result, TwoSumTrace.flags, Flags.union]

/-- Total schedule refinement, including exceptional operands and all six flag sets. -/
theorem twoSum_spec (I : Interchange) [I.Valid] (a b : I.Word) : Spec.TwoSum I a b (twoSum I a b) := by
  let t := twoSumTrace I a b
  exact ⟨t.sum,t.bvirt,t.avirt,t.bround,t.around,t.error,
    add_spec I .nearestEven a b, sub_spec I .nearestEven _ _, sub_spec I .nearestEven _ _,
    sub_spec I .nearestEven _ _, sub_spec I .nearestEven _ _, add_spec I .nearestEven _ _, rfl,rfl⟩

/-- Static sufficient reconstruction conditions, expressed as representability,
not as assumptions of operation error or exactness. -/
theorem certifiedTwoSum?_complete (I : Interchange) [I.Valid] (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv)
    (hav : I.format.Representable ((s-bv : ℚ) : ℝ))
    (hbr : I.format.Representable ((y-bv : ℚ) : ℝ))
    (har : I.format.Representable ((x-(s-bv) : ℚ) : ℝ))
    (he : I.format.Representable (((x-(s-bv))+(y-bv) : ℚ) : ℝ)) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  have exact_flags (op : BinaryOp) (u v : I.Word) (p q : ℚ)
      (hp : (Datum.decode I u).toRat? = some p) (hq : (Datum.decode I v).toRat? = some q)
      (hr : I.format.Representable (binaryExact op p q : ℝ)) :
      (binary I op .nearestEven u v).flags = Flags.empty := by
    rw [binary_finite I op .nearestEven u v p q hp hq]
    exact (roundWithMode_exact I .nearestEven _ _ hr).2
  have fav := exact_flags .sub _ _ s bv hs hv hav
  have dav := binary_exact_of_no_flags I .sub .nearestEven _ _ s bv hs hv fav
  have fbr := exact_flags .sub _ _ y bv hb hv hbr
  have dbr := binary_exact_of_no_flags I .sub .nearestEven _ _ y bv hb hv fbr
  have far := exact_flags .sub _ _ x (s-bv) ha dav har
  have dar := binary_exact_of_no_flags I .sub .nearestEven _ _ x (s-bv) ha dav far
  have fe := exact_flags .add _ _ (x-(s-bv)) (y-bv) dar dbr he
  have fin (w : I.Word) (q : ℚ) (h : (Datum.decode I w).toRat? = some q) :
      (Datum.decode I w).isFinite = true := by
    rw [← Datum.toRat?_isSome, h]; rfl
  change (twoSumTrace I a b).avirt.flags = Flags.empty at fav
  change (twoSumTrace I a b).bround.flags = Flags.empty at fbr
  change (twoSumTrace I a b).around.flags = Flags.empty at far
  change (twoSumTrace I a b).error.flags = Flags.empty at fe
  have hc : (twoSumTrace I a b).checked = true := by
    simp only [TwoSumTrace.checked, fin _ s hs, fin _ bv hv,
      (flagsClear_iff _).mpr fav, (flagsClear_iff _).mpr fbr,
      (flagsClear_iff _).mpr far, (flagsClear_iff _).mpr fe]
    rfl
  simp [certifiedTwoSum?, fin a x ha, fin b y hb, hc, twoSum]

/-- The rational field value is safe to use after finite decoding succeeds. -/
def wordRat (I : Interchange) (a : I.Word) : ℚ := (Datum.decode I a).fields.rationalValue

theorem wordRat_of_decode (I : Interchange) (a : I.Word) (x : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) : wordRat I a = x := by
  unfold wordRat
  generalize hd : Datum.decode I a = d at ha ⊢
  cases d <;> simp_all [Datum.toRat?, Datum.isFinite]

/-- Finiteness of a nearest-even result derives its mixed error bound, including underflow. -/
theorem binary_even_error_of_decode (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y z : ℚ) (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hz : (Datum.decode I (binary I op .nearestEven a b).value).toRat? = some z) :
    |(z : ℝ) - (binaryExact op x y : ℝ)| ≤
      I.format.unitRoundoff * |(binaryExact op x y : ℝ)| + I.format.minSubnormal/2 := by
  have hp := binary_even_projection I op a b x y ha hb
  rw [hz] at hp
  unfold roundNearest? at hp
  split_ifs at hp with hno
  have he : z = scaledRound I.format .nearestEven (binaryExact op x y) := Option.some.inj hp
  rw [he, scaledRound_even_cast]
  exact I.format.roundFinite_mixed_error _

/-- Exact finite arithmetic from representability, with rational decoding and all flags. -/
theorem binary_exact_of_representable (I : Interchange) [I.Valid] (op : BinaryOp) (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ) (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (h : I.format.Representable (binaryExact op x y : ℝ)) :
    (Datum.decode I (binary I op mode a b).value).toRat? = some (binaryExact op x y) ∧
      (binary I op mode a b).flags = Flags.empty := by
  have hf : (binary I op mode a b).flags = Flags.empty := by
    rw [binary_finite I op mode a b x y ha hb]
    exact (roundWithMode_exact I mode _ _ h).2
  exact ⟨binary_exact_of_no_flags I op mode a b x y ha hb hf,hf⟩

/-- No reconstruction hypotheses are needed when the exact input sum is representable. -/
theorem certifiedTwoSum?_of_exact_sum (I : Interchange) [I.Valid] (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hxy : I.format.Representable ((x+y : ℚ) : ℝ)) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  have hx := rat_representable_of_decode I a x ha
  have hy := rat_representable_of_decode I b y hb
  have hs := (binary_exact_of_representable I .add .nearestEven a b x y ha hb hxy).1
  have hv := (binary_exact_of_representable I .sub .nearestEven _ a (x+y) x hs ha
    (by simpa [binaryExact] using hy)).1
  have hv' : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some y := by
    simpa [twoSumTrace, sub, add, binaryExact] using hv
  apply certifiedTwoSum?_complete I a b x y (x+y) y ha hb hs hv'
  · simpa using hx
  · simpa using I.format.representable_zero
  · simpa using I.format.representable_zero
  · simpa using I.format.representable_zero

/-- An absorbed addend is recovered without extra reconstruction assumptions. -/
theorem certifiedTwoSum?_of_absorbed (I : Interchange) [I.Valid] (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (add I .nearestEven a b).value).toRat? = some x) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  have hx := rat_representable_of_decode I a x ha
  have hy := rat_representable_of_decode I b y hb
  have hv := (binary_exact_of_representable I .sub .nearestEven _ a x x hs ha
    (by simpa [binaryExact] using I.format.representable_zero)).1
  have hv' : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some 0 := by
    simpa [twoSumTrace, sub, add, binaryExact] using hv
  apply certifiedTwoSum?_complete I a b x y x 0 ha hb hs hv'
  · simpa using hx
  · simpa using hy
  · simpa using I.format.representable_zero
  · simpa using hy
end FP.IEEE.Software
