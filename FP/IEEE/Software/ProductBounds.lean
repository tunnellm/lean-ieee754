import FP.IEEE.ProductRoundoff
import FP.IEEE.Software.Cancellation
import FP.IEEE.Spec.TwoProduct

/-! Word-level exact and bounded TwoProduct guarantees, including residual underflow. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

theorem twoProduct_spec (I : Interchange) [I.Valid] (a b : I.Word) :
    Spec.TwoProduct I a b (twoProduct I a b) := by
  refine ⟨mul I .nearestEven a b,productResidual I a b,mul_spec I .nearestEven a b,?_,rfl,rfl⟩
  have he : (negate I (mul I .nearestEven a b).value).value =
      ((Datum.decode I (mul I .nearestEven a b).value).withSign
        (!(Datum.decode I (mul I .nearestEven a b).value).fields.negative)).encode := by
    simp [negate,Result.pure,Datum.encode,Datum.decode]
  simpa only [productResidual,← he] using fma_spec I .nearestEven a b (negate I (mul I .nearestEven a b).value).value

theorem finite_toRat_wordRat (I : Interchange) (w : I.Word)
    (h : (Datum.decode I w).isFinite = true) : (Datum.decode I w).toRat? = some (wordRat I w) := by
  simp [Datum.toRat?,wordRat,h]

theorem finite_of_toRat (I : Interchange) (w : I.Word) (q : ℚ)
    (h : (Datum.decode I w).toRat? = some q) : (Datum.decode I w).isFinite = true := by
  simpa only [Datum.toRat?_isSome,Option.isSome_some] using congrArg Option.isSome h

theorem binary_even_range_of_decode (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y z : ℚ) (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hz : (Datum.decode I (binary I op .nearestEven a b).value).toRat? = some z) :
    |(binaryExact op x y : ℝ)| < I.format.overflowThreshold := by
  have hh := binary_even_projection I op a b x y ha hb
  rw [hz] at hh
  unfold roundNearest? at hh
  split_ifs at hh with h
  simpa only [← overflowThreshold_cast] using (show |(binaryExact op x y : ℝ)| < (overflowThreshold I.format : ℝ) by exact_mod_cast h)

theorem binary_even_finite_of_real_range (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y : ℚ) (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (h : |(binaryExact op x y : ℝ)| < I.format.overflowThreshold) :
    (Datum.decode I (binary I op .nearestEven a b).value).isFinite = true := by
  have hq : |binaryExact op x y| < overflowThreshold I.format := by
    have hh : |(binaryExact op x y : ℝ)| < (overflowThreshold I.format : ℝ) := by simpa using h
    exact_mod_cast hh
  apply finite_of_toRat I _ (scaledRound I.format .nearestEven (binaryExact op x y))
  rw [binary_even_projection I op a b x y ha hb]
  simp [roundNearest?,hq]

/-- A finite product implies a finite FMA residual. Its only possible numerical
loss is bounded by half a least subnormal, even when the product is normal. -/
theorem twoProduct_bounded_of_finite (I : Interchange) [I.Valid] (a b : I.Word) (x y p : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hp : (Datum.decode I (mul I .nearestEven a b).value).toRat? = some p) :
    ∃ e : ℚ, (Datum.decode I (productResidual I a b).value).toRat? = some e ∧
      |((x*y-p-e : ℚ) : ℝ)| ≤ I.format.minSubnormal/2 := by
  have hr := binary_even_range_of_decode I .mul a b x y p ha hb hp
  have hpr := binary_even_roundFinite_of_decode I .mul a b x y p ha hb hp
  simp only [binaryExact,Rat.cast_mul] at hr hpr
  have hres : |(x : ℝ)*(y : ℝ)-(p : ℝ)| < I.format.overflowThreshold := by
    have hn := I.format.roundFinite_nearest ((x : ℝ)*(y : ℝ)) 0 I.format.representable_zero
    simpa [hpr,abs_sub_comm] using hn.trans_lt (by simpa using hr)
  have hd : I.decode? (productResidual I a b).value =
      some (I.format.roundFinite ((x : ℝ)*(y : ℝ)-(p : ℝ))) := by
    rw [productResidual_finite I a b x y p ha hb hp,roundWithMode_even_cast]
    simp [Format.round?,hres]
  have he := Datum.toRat?_decode I (productResidual I a b).value
  rw [hd] at he
  obtain ⟨e,heq,hev⟩ := Option.map_eq_some_iff.mp he
  refine ⟨e,heq,?_⟩
  have herr := I.format.roundFinite_product_residual_error
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb) hr
  simpa [Rat.cast_sub,Rat.cast_mul,hev,hpr,abs_sub_comm] using herr

theorem productResidual_isFinite (I : Interchange) [I.Valid] (a b : I.Word)
    (ha : (Datum.decode I a).isFinite = true) (hb : (Datum.decode I b).isFinite = true)
    (hp : (Datum.decode I (mul I .nearestEven a b).value).isFinite = true) :
    (Datum.decode I (productResidual I a b).value).isFinite = true := by
  obtain ⟨e,he,_⟩ := twoProduct_bounded_of_finite I a b _ _ _
    (finite_toRat_wordRat I a ha) (finite_toRat_wordRat I b hb) (finite_toRat_wordRat I _ hp)
  exact finite_of_toRat I _ e he

/-- Canonical word exponents give an input-only sufficient lattice condition. -/
def TwoProductRange (I : Interchange) (a b : I.Word) : Prop :=
  (Datum.decode I a).isFinite = true ∧ (Datum.decode I b).isFinite = true ∧
  |wordRat I a*wordRat I b| < overflowThreshold I.format ∧
  (wordRat I a = 0 ∨ wordRat I b = 0 ∨
    I.format.emin-I.format.fractionBits ≤ I.scaleExponent a+I.scaleExponent b)

instance (I : Interchange) (a b : I.Word) : Decidable (TwoProductRange I a b) := by
  unfold TwoProductRange; infer_instance

private theorem decoded_lattice (I : Interchange) [I.Valid] (a : I.Word) (x : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) :
    ∃ k : ℤ, (x : ℝ) = (k : ℝ)*2^(I.scaleExponent a) ∧ |(k : ℝ)| < (2 : ℝ)^I.format.precision := by
  have hv := Datum.toRat?_decode I a
  rw [ha] at hv
  simp only [Option.map_some,Interchange.decode?] at hv
  split_ifs at hv
  have hx : (x : ℝ) = I.value a := Option.some.inj hv
  have hm : I.mantissa a < 2^I.format.precision := by
    have hf : I.fraction a < 2^I.format.fractionBits := Nat.mod_lt _ (by positivity)
    unfold Interchange.mantissa Format.precision
    rw [pow_succ]; split_ifs <;> omega
  have hmR : (I.mantissa a : ℝ) < (2 : ℝ)^I.format.precision := by exact_mod_cast hm
  rw [hx]
  by_cases hs : I.negative a = true
  · exact ⟨-(I.mantissa a : ℤ),by simp [Interchange.value,hs],by simpa using hmR⟩
  · exact ⟨(I.mantissa a : ℤ),by simp [Interchange.value,hs],by simpa using hmR⟩

theorem TwoProductRange.residual_representable (I : Interchange) [I.Valid] (a b : I.Word)
    (h : TwoProductRange I a b) :
    I.format.Representable ((wordRat I a : ℝ)*(wordRat I b : ℝ)-
      I.format.roundFinite ((wordRat I a : ℝ)*(wordRat I b : ℝ))) := by
  have hr : |(wordRat I a : ℝ)*(wordRat I b : ℝ)| < I.format.overflowThreshold := by
    have hh : |((wordRat I a*wordRat I b : ℚ) : ℝ)| < (overflowThreshold I.format : ℝ) := by exact_mod_cast h.2.2.1
    simpa using hh
  rcases h.2.2.2 with hz | hz | hl
  · simp [hz,I.format.representable_zero]
  · simp [hz,I.format.representable_zero]
  · obtain ⟨m,hm,hmb⟩ := decoded_lattice I a _ (finite_toRat_wordRat I a h.1)
    obtain ⟨n,hn,hnb⟩ := decoded_lattice I b _ (finite_toRat_wordRat I b h.2.1)
    have he : (wordRat I a : ℝ)*(wordRat I b : ℝ) =
        ((m*n : ℤ) : ℝ)*2^(I.scaleExponent a+I.scaleExponent b) := by
      rw [hm,hn,zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      push_cast; ring
    rw [he] at hr ⊢
    apply I.format.roundFinite_residual_representable_of_wide_lattice _ _ _ hl hr
    rw [Int.cast_mul,abs_mul,show 2*I.format.precision = I.format.precision+I.format.precision by omega,pow_add]
    exact (mul_le_mul_of_nonneg_right hmb.le (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left hnb (by positivity))

theorem certifiedTwoProduct?_of_range (I : Interchange) [I.Valid] (a b : I.Word)
    (h : TwoProductRange I a b) : certifiedTwoProduct? I a b = some (twoProduct I a b) := by
  have ha := finite_toRat_wordRat I a h.1
  have hb := finite_toRat_wordRat I b h.2.1
  have hr : |(binaryExact .mul (wordRat I a) (wordRat I b) : ℝ)| < I.format.overflowThreshold := by
    have hh : |((wordRat I a*wordRat I b : ℚ) : ℝ)| < (overflowThreshold I.format : ℝ) := by exact_mod_cast h.2.2.1
    simpa [binaryExact] using hh
  have hp := finite_toRat_wordRat I _ (binary_even_finite_of_real_range I .mul a b _ _ ha hb hr)
  have hpr := binary_even_roundFinite_of_decode I .mul a b _ _ _ ha hb hp
  apply certifiedTwoProduct?_complete I a b _ _ _ ha hb hp
  simpa [Rat.cast_sub,Rat.cast_mul,binaryExact,hpr] using TwoProductRange.residual_representable I a b h

/-- Under finite operands/high product, exact-certificate success is precisely
residual representability; the static exponent test is only sufficient. -/
theorem certifiedTwoProduct?_success_iff_representable (I : Interchange) [I.Valid]
    (a b : I.Word) (x y p : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hp : (Datum.decode I (mul I .nearestEven a b).value).toRat? = some p) :
    (certifiedTwoProduct? I a b).isSome = true ↔ I.format.Representable ((x*y-p : ℚ) : ℝ) := by
  constructor
  · intro h
    have hf : flagsClear (productResidual I a b).flags = true := by
      simpa [certifiedTwoProduct?,hp] using h
    have he := (flagsClear_iff _).mp hf
    rw [productResidual_finite I a b x y p ha hb hp] at he
    have hd := roundWithMode_exact_of_no_flags I .nearestEven (x*y-p) _ he
    have hm := Datum.toRat?_decode I (roundWithMode I .nearestEven (x*y-p)
      (Spec.fmaZeroSign .nearestEven (Datum.decode I a) (Datum.decode I b)
        (Datum.decode I (negate I (mul I .nearestEven a b).value).value))).value
    rw [hd] at hm
    obtain ⟨q,hq,hv⟩ := Option.map_eq_some_iff.mp hm
    rw [← hv]
    exact rat_representable_of_decode I _ q hq
  · intro he
    rw [certifiedTwoProduct?_complete I a b x y p ha hb hp he]
    rfl

end FP.IEEE.Software
