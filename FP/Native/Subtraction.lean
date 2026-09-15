import FP.Native.Bridge

/-! Native subtraction, reduced to the already verified unpacked addition.
The packed refinement retains the explicit finite/nonoverflow qualifications. -/
noncomputable section
namespace FP.Native
open Float.Model
open Float.Model.UnpackedFloat

private theorem neg_sign_apply (s : Sign) (m : ℤ) : (-s).apply m = -s.apply m := by
  cases s <;> simp [Sign.apply]

/-- An identity of the native logical operations, including exceptional operands. -/
theorem sub_unpacked_eq_add_neg (S : Float.Model.Format) (a b : UnpackedFloat) :
    UnpackedFloat.sub S a b = UnpackedFloat.add S a (UnpackedFloat.neg b) := by
  cases a <;> cases b <;>
    simp [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg,
      neg_sign_apply, sub_eq_add_neg]

theorem neg_unpacked_value (a : UnpackedFloat) :
    unpackedValue (UnpackedFloat.neg a) = (unpackedValue a).map (fun x => -x) := by
  cases a <;> simp [UnpackedFloat.neg, unpackedValue, neg_sign_apply, neg_mul]

theorem neg_unpacked_canonical (S : Float.Model.Format) (a : UnpackedFloat)
    (ha : Canonical S a) : Canonical S (UnpackedFloat.neg a) := by
  cases a <;> simp_all [Canonical, UnpackedFloat.neg]

theorem sub_unpacked {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (a b : UnpackedFloat) (x y : ℝ)
    (ha : Canonical S a) (hb : Canonical S b)
    (hax : unpackedValue a = some x) (hby : unpackedValue b = some y) :
    Canonical S (UnpackedFloat.sub S a b) ∧
      unpackedValue (UnpackedFloat.sub S a b) = some (F.roundFinite (x - y)) := by
  rw [sub_unpacked_eq_add_neg]
  have hneg : unpackedValue (UnpackedFloat.neg b) = some (-y) := by
    rw [neg_unpacked_value, hby]; rfl
  simpa only [sub_eq_add_neg] using
    add_unpacked hSF a (UnpackedFloat.neg b) x (-y) ha
      (neg_unpacked_canonical S b hb) hax hneg

theorem sub_words {S : Float.Model.Format} {F : FP.IEEE.Format}
    (hSF : FormatAgreement S F) (hmax : F.emax = (S.exponentBias : ℤ))
    (a b : BitVec S.numBits) (x y : ℝ)
    (hax : wordValue S a = some x) (hby : wordValue S b = some y)
    (hr : |x - y| < F.overflowThreshold) :
    wordValue S (pack S (UnpackedFloat.sub S (unpack S a) (unpack S b))) =
      F.round? (x - y) := by
  obtain ⟨hc, hv⟩ := sub_unpacked hSF (unpack S a) (unpack S b) x y
    (unpack_canonical S a x hax) (unpack_canonical S b y hby) hax hby
  rw [pack_value hSF hmax _ _ hc hv (F.roundFinite_representable hr)]
  simp only [FP.IEEE.Format.round?, if_pos hr]

theorem float_sub_equiv (a b : Float) (x y : ℝ)
    (ha : floatValue a = some x) (hb : floatValue b = some y)
    (hr : |x - y| < FP.IEEE.binary64.overflowThreshold) :
    floatValue (a - b) = FP.IEEE.binary64.round? (x - y) := by
  exact sub_words binary64_agreement (by norm_num [FP.IEEE.binary64,
    Float.Model.Format.binary64, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

theorem float32_sub_equiv (a b : Float32) (x y : ℝ)
    (ha : float32Value a = some x) (hb : float32Value b = some y)
    (hr : |x - y| < FP.IEEE.binary32.overflowThreshold) :
    float32Value (a - b) = FP.IEEE.binary32.round? (x - y) := by
  exact sub_words binary32_agreement (by norm_num [FP.IEEE.binary32,
    Float.Model.Format.binary32, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

end FP.Native
