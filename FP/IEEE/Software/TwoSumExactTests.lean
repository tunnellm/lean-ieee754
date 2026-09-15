import FP.IEEE.Software.TwoSumExact

/-! General theorem applications and kernel regressions at IEEE TwoSum boundaries. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange

/-- Arbitrary fp32 inputs: only the first two result decodings are hypotheses. -/
example (a b : fp32.Word) (x y s bv : ℚ)
    (ha : (Datum.decode fp32 a).toRat? = some x)
    (hb : (Datum.decode fp32 b).toRat? = some y)
    (hs : (Datum.decode fp32 (twoSumTrace fp32 a b).sum.value).toRat? = some s)
    (hv : (Datum.decode fp32 (twoSumTrace fp32 a b).bvirt.value).toRat? = some bv) :
    (Datum.decode fp32 (twoSum fp32 a b).value.2).toRat? = some (x+y-s) :=
  (twoSum_exact_of_finite_stages fp32 a b x y s bv ha hb hs hv).2

example (a b : fp64.Word) (x y s bv : ℚ)
    (ha : (Datum.decode fp64 a).toRat? = some x)
    (hb : (Datum.decode fp64 b).toRat? = some y)
    (hs : (Datum.decode fp64 (twoSumTrace fp64 a b).sum.value).toRat? = some s)
    (hv : (Datum.decode fp64 (twoSumTrace fp64 a b).bvirt.value).toRat? = some bv) :
    (Datum.decode fp64 (twoSum fp64 a b).value.2).toRat? = some (x+y-s) :=
  (twoSum_exact_of_finite_stages fp64 a b x y s bv ha hb hs hv).2

/-- Both reconstruction corrections can be nonzero at a binade boundary. -/
example :
    let t := twoSumTrace fp32 0x3fffffff 0x40000001
    t.sum.value = 0x40800000 ∧ t.bvirt.value = 0x40000000 ∧
    t.around.value = 0xb4000000 ∧ t.bround.value = 0x34800000 ∧
    t.error.value = 0x34000000 ∧ flagsClear t.avirt.flags = true ∧
    flagsClear t.bround.flags = true ∧ flagsClear t.around.flags = true ∧
    flagsClear t.error.flags = true := by decide +kernel

example :
    let t := twoSumTrace fp64 0x3fffffffffffffff 0x4000000000000001
    t.sum.value = 0x4010000000000000 ∧ t.bvirt.value = 0x4000000000000000 ∧
    t.around.value = 0xbcb0000000000000 ∧ t.bround.value = 0x3cc0000000000000 ∧
    t.error.value = 0x3cb0000000000000 ∧ flagsClear t.avirt.flags = true ∧
    flagsClear t.bround.flags = true ∧ flagsClear t.around.flags = true ∧
    flagsClear t.error.flags = true := by decide +kernel

/-- General completeness certifies this case without executing reconstruction checks. -/
example : certifiedTwoSum? fp32 0x3fffffff 0x40000001 =
    some (twoSum fp32 0x3fffffff 0x40000001) := by
  apply (certifiedTwoSum?_success_iff_finite_stages fp32 _ _).mpr
  decide +kernel

example : certifiedTwoSum? fp64 0x3fffffffffffffff 0x4000000000000001 =
    some (twoSum fp64 0x3fffffffffffffff 0x4000000000000001) := by
  apply (certifiedTwoSum?_success_iff_finite_stages fp64 _ _).mpr
  decide +kernel

/-- Midpoint absorption, swapped order, sign symmetry, and negative zero. -/
example : [twoSum fp32 0x3f800000 0x33800000, twoSum fp32 0x33800000 0x3f800000,
    twoSum fp32 0xbf800000 0xb3800000, twoSum fp32 0x80000000 0x80000000].map
      (fun r => r.value) =
    [(0x3f800000#32,0x33800000#32), (0x3f800000#32,0x33800000#32),
     (0xbf800000#32,0xb3800000#32), (0x80000000#32,0#32)] := by decide +kernel

/-- Exact cancellation can reach the least subnormal without underflow flags. -/
example : (twoSum fp32 0x00800001 0x80800000).value = (1#32,0#32) ∧
    flagsClear (twoSum fp32 0x00800001 0x80800000).flags = true ∧
    (twoSum fp64 0x0010000000000001 0x8010000000000000).value = (1#64,0#64) ∧
    flagsClear (twoSum fp64 0x0010000000000001 0x8010000000000000).flags = true := by decide +kernel

/-- Inexact bvirt is permitted by the general theorem. -/
example : (Datum.decode fp32 (twoSum fp32 0xbf800000 0x4c000000).value.2).toRat? = some (-1) := by
  have h := twoSum_exact_of_finite_stages fp32 0xbf800000 0x4c000000
    (-1) (2^25) (2^25) (2^25)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num at h
  exact h.2

example : (twoSumTrace fp32 0xbf800000 0x4c000000).bvirt.flags .inexact = true ∧
    (twoSumTrace fp64 0xbff0000000000000 0x4350000000000000).bvirt.flags .inexact = true := by
  decide +kernel

/-- Finite initial sums do not exclude intermediate overflow. The additional
bvirt-finiteness hypothesis cannot be dropped from the general theorem. -/
theorem twoSum_intermediate_overflow_fp32 :
    (Datum.decode fp32 0xf3c00000).isFinite = true ∧
    (Datum.decode fp32 0x7f7fffff).isFinite = true ∧
    (twoSumTrace fp32 0xf3c00000 0x7f7fffff).sum.value = 0x7f7ffffe ∧
    (Datum.decode fp32 (twoSumTrace fp32 0xf3c00000 0x7f7fffff).sum.value).isFinite = true ∧
    (twoSumTrace fp32 0xf3c00000 0x7f7fffff).bvirt.flags .overflow = true ∧
    (Datum.decode fp32 (twoSum fp32 0xf3c00000 0x7f7fffff).value.2).isNaN = true ∧
    (certifiedTwoSum? fp32 0xf3c00000 0x7f7fffff).isNone = true := by decide +kernel

theorem twoSum_intermediate_overflow_fp64 :
    (Datum.decode fp64 0xfca8000000000000).isFinite = true ∧
    (Datum.decode fp64 0x7fefffffffffffff).isFinite = true ∧
    (twoSumTrace fp64 0xfca8000000000000 0x7fefffffffffffff).sum.value = 0x7feffffffffffffe ∧
    (Datum.decode fp64 (twoSumTrace fp64 0xfca8000000000000 0x7fefffffffffffff).sum.value).isFinite = true ∧
    (twoSumTrace fp64 0xfca8000000000000 0x7fefffffffffffff).bvirt.flags .overflow = true ∧
    (Datum.decode fp64 (twoSum fp64 0xfca8000000000000 0x7fefffffffffffff).value.2).isNaN = true ∧
    (certifiedTwoSum? fp64 0xfca8000000000000 0x7fefffffffffffff).isNone = true := by decide +kernel

/-- Exceptional inputs and overflowing sums remain outside numerical exactness. -/
example : (certifiedTwoSum? fp32 0x7f7fffff 0x7f7fffff).isNone = true ∧
    (certifiedTwoSum? fp32 0x7fc00123 0x3f800000).isNone = true ∧
    (certifiedTwoSum? fp64 0x7ff0000000000000 0x3ff0000000000000).isNone = true := by decide +kernel

end FP.IEEE.Software.Tests
