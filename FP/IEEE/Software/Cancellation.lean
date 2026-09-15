import FP.IEEE.Roundoff
import FP.IEEE.Software.TwoSum

/-! Exact cancellation and representable roundoff for executable IEEE words. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Sterbenz subtraction is exact in every rounding mode, with no raised flags.
This includes subnormal operands and subnormal exact results. -/
theorem sub_sterbenz (I : Interchange) [I.Valid] (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hxy : x/2 ≤ y) (hyx : y ≤ 2*x) :
    (Datum.decode I (sub I mode a b).value).toRat? = some (x-y) ∧
      (sub I mode a b).flags = Flags.empty := by
  apply binary_exact_of_representable I .sub mode a b x y ha hb
  simpa [binaryExact] using I.format.sterbenz
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb)
    (by exact_mod_cast hxy) (by exact_mod_cast hyx)

/-- Signed-magnitude form of exact IEEE subtraction. -/
theorem sub_sterbenz_abs (I : Interchange) [I.Valid] (mode : RoundingMode)
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hsign : 0 ≤ x*y) (hxy : |x|/2 ≤ |y|) (hyx : |y| ≤ 2*|x|) :
    (Datum.decode I (sub I mode a b).value).toRat? = some (x-y) ∧
      (sub I mode a b).flags = Flags.empty := by
  apply binary_exact_of_representable I .sub mode a b x y ha hb
  simpa [binaryExact] using I.format.sterbenz_abs
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb)
    (by exact_mod_cast hsign) (by exact_mod_cast hxy) (by exact_mod_cast hyx)

/-- Recover the real rounding equation from finite IEEE input/output decoding. -/
theorem binary_even_roundFinite_of_decode (I : Interchange) [I.Valid] (op : BinaryOp)
    (a b : I.Word) (x y z : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hz : (Datum.decode I (binary I op .nearestEven a b).value).toRat? = some z) :
    (z : ℝ) = I.format.roundFinite (binaryExact op x y : ℝ) := by
  have h := binary_even_projection I op a b x y ha hb
  rw [hz] at h
  unfold roundNearest? at h
  split_ifs at h with hn
  have he := Option.some.inj h
  rw [he]
  exact scaledRound_even_cast I.format _

/-- A finite nearest-even addition has an exactly representable residual. -/
theorem add_residual_representable (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (add I .nearestEven a b).value).toRat? = some s) :
    I.format.Representable ((x+y-s : ℚ) : ℝ) := by
  have he := binary_even_roundFinite_of_decode I .add a b x y s ha hb hs
  simp only [binaryExact, Rat.cast_add] at he
  simp only [Rat.cast_sub, Rat.cast_add, he]
  exact I.format.roundFinite_add_residual_representable
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb)

/-- A finite nearest-even subtraction has an exactly representable residual. -/
theorem sub_residual_representable (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (sub I .nearestEven a b).value).toRat? = some s) :
    I.format.Representable ((x-y-s : ℚ) : ℝ) := by
  have he := binary_even_roundFinite_of_decode I .sub a b x y s ha hb hs
  simp only [binaryExact, Rat.cast_sub] at he
  simp only [Rat.cast_sub, he]
  exact I.format.roundFinite_sub_residual_representable
    (rat_representable_of_decode I a x ha) (rat_representable_of_decode I b y hb)

/-- Two reconstruction hypotheses suffice: representability of `around` and of
the final error follows automatically from the rounding-residual theorems. -/
theorem certifiedTwoSum?_of_two_reconstructions (I : Interchange) [I.Valid]
    (a b : I.Word) (x y s bv : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hs : (Datum.decode I (twoSumTrace I a b).sum.value).toRat? = some s)
    (hv : (Datum.decode I (twoSumTrace I a b).bvirt.value).toRat? = some bv)
    (hav : I.format.Representable ((s-bv : ℚ) : ℝ))
    (hbr : I.format.Representable ((y-bv : ℚ) : ℝ)) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  have har := I.format.representable_neg
    (sub_residual_representable I _ a s x bv hs ha hv)
  have he := add_residual_representable I a b x y s ha hb hs
  apply certifiedTwoSum?_complete I a b x y s bv ha hb hs hv hav hbr
  · convert har using 1
    push_cast
    ring
  · convert he using 1
    push_cast
    ring

/-- Cancellation within a factor of two certifies TwoSum automatically, without
any reconstruction or nonoverflow assumptions. -/
theorem certifiedTwoSum?_of_cancellation (I : Interchange) [I.Valid]
    (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x)
    (hb : (Datum.decode I b).toRat? = some y)
    (hsign : x*y ≤ 0) (hxy : |x|/2 ≤ |y|) (hyx : |y| ≤ 2*|x|) :
    certifiedTwoSum? I a b = some (twoSum I a b) := by
  apply certifiedTwoSum?_of_exact_sum I a b x y ha hb
  have hx := rat_representable_of_decode I a x ha
  have hy := I.format.representable_neg (rat_representable_of_decode I b y hb)
  have hsign' : (0 : ℝ) ≤ (x : ℝ)*(-(y : ℝ)) := by
    have h : (x : ℝ)*(y : ℝ) ≤ 0 := by exact_mod_cast hsign
    nlinarith
  have h := I.format.sterbenz_abs hx hy hsign'
    (by simpa using (show |(x : ℝ)|/2 ≤ |(y : ℝ)| by exact_mod_cast hxy))
    (by simpa using (show |(y : ℝ)| ≤ 2*|(x : ℝ)| by exact_mod_cast hyx))
  simpa using h

end FP.IEEE.Software
