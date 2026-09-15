import FP.Native.Operations

/-! Equivalence for Lean's native floating-point operations on finite values.
The proofs unfold the native logical model; they do not use native evaluation. -/
noncomputable section
namespace FP.Native

/-- Exact finite real projection; exceptional values have no projection. -/
def floatValue (a : Float) : Option ℝ :=
  wordValue Float.Model.Format.binary64 a.toBits.toBitVec

def float32Value (a : Float32) : Option ℝ :=
  wordValue Float.Model.Format.binary32 a.toBits.toBitVec

theorem floatValue_decode (a : Float) :
    floatValue a = FP.IEEE.fp64.decode? a.toBits.toBitVec :=
  wordValue_binary64 _

theorem float32Value_decode (a : Float32) :
    float32Value a = FP.IEEE.fp32.decode? a.toBits.toBitVec :=
  wordValue_binary32 _

theorem float_add_equiv (a b : Float) (x y : ℝ)
    (ha : floatValue a = some x) (hb : floatValue b = some y)
    (hr : |x + y| < FP.IEEE.binary64.overflowThreshold) :
    floatValue (a + b) = FP.IEEE.binary64.round? (x + y) := by
  exact add_words binary64_agreement (by norm_num [FP.IEEE.binary64,
    Float.Model.Format.binary64, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

theorem float_mul_equiv (a b : Float) (x y : ℝ)
    (ha : floatValue a = some x) (hb : floatValue b = some y)
    (hr : |x * y| < FP.IEEE.binary64.overflowThreshold) :
    floatValue (a * b) = FP.IEEE.binary64.round? (x * y) := by
  exact mul_words binary64_agreement (by norm_num [FP.IEEE.binary64,
    Float.Model.Format.binary64, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

theorem float32_add_equiv (a b : Float32) (x y : ℝ)
    (ha : float32Value a = some x) (hb : float32Value b = some y)
    (hr : |x + y| < FP.IEEE.binary32.overflowThreshold) :
    float32Value (a + b) = FP.IEEE.binary32.round? (x + y) := by
  exact add_words binary32_agreement (by norm_num [FP.IEEE.binary32,
    Float.Model.Format.binary32, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

theorem float32_mul_equiv (a b : Float32) (x y : ℝ)
    (ha : float32Value a = some x) (hb : float32Value b = some y)
    (hr : |x * y| < FP.IEEE.binary32.overflowThreshold) :
    float32Value (a * b) = FP.IEEE.binary32.round? (x * y) := by
  exact mul_words binary32_agreement (by norm_num [FP.IEEE.binary32,
    Float.Model.Format.binary32, Float.Model.Format.exponentBias])
    a.toBits.toBitVec b.toBits.toBitVec x y ha hb hr

@[simp] theorem floatValue_zero : floatValue (Float.ofBits 0) = some 0 := by
  change unpackedValue (.zero .positive) = some 0
  rfl

@[simp] theorem float32Value_zero : float32Value (Float32.ofBits 0) = some 0 := by
  change unpackedValue (.zero .positive) = some 0
  rfl

end FP.Native
