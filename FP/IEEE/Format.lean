import FP.IEEE.Rounding

/-! Binary interchange formats and their exact real-value rounding semantics.
`round?` is the finite projection: `none` denotes overflow to signed infinity.
NaN/infinite operands and signed-zero distinctions are outside this projection.
-/
noncomputable section
namespace FP.IEEE

/-- `emin` and `emax` are unbiased normal exponents; precision is `fractionBits+1`. -/
structure Format where
  fractionBits : ℕ
  emin : ℤ
  emax : ℤ
  exponent_order : emin ≤ emax

def binary32 : Format := ⟨23, -126, 127, by norm_num⟩
def binary64 : Format := ⟨52, -1022, 1023, by norm_num⟩

namespace Format

def precision (F : Format) : ℕ := F.fractionBits + 1
def unitRoundoff (F : Format) : ℝ := (2 : ℝ) ^ (-(F.fractionBits : ℤ) - 1)
def minNormal (F : Format) : ℝ := (2 : ℝ) ^ F.emin
def minSubnormal (F : Format) : ℝ := (2 : ℝ) ^ (F.emin - F.fractionBits)
def maxFinite (F : Format) : ℝ :=
  ((2 : ℝ) ^ (F.fractionBits + 1) - 1) * (2 : ℝ) ^ (F.emax - F.fractionBits)

/-- Midpoint between the largest finite number and the next binade.
At equality, ties-to-even overflows to infinity. -/
def overflowThreshold (F : Format) : ℝ :=
  ((2 : ℝ) ^ (F.fractionBits + 1) - 1 / 2) * (2 : ℝ) ^ (F.emax - F.fractionBits)

/-- The least significant bit's exponent, clamped for gradual underflow. -/
def quantumExponent (F : Format) (x : ℝ) : ℤ :=
  max F.emin (Int.log 2 |x|) - F.fractionBits

def quantum (F : Format) (x : ℝ) : ℝ := (2 : ℝ) ^ F.quantumExponent x

/-- Unbounded-exponent rounding, with the IEEE lower exponent bound. -/
def roundFinite (F : Format) (x : ℝ) : ℝ :=
  (roundEven (x / F.quantum x) : ℝ) * F.quantum x

/-- Exact IEEE nearest-even rounding of a finite real input, projected to finite
real values. Overflow has no real value and is represented by `none`. -/
def round? (F : Format) (x : ℝ) : Option ℝ :=
  if |x| < F.overflowThreshold then some (F.roundFinite x) else none

/-- A sufficient normal-range condition on the exact input to an operation.
Zero is allowed, so exact cancellation is not excluded. -/
def Safe (F : Format) (x : ℝ) : Prop :=
  x = 0 ∨ F.minNormal ≤ |x| ∧ |x| < F.overflowThreshold

/-- The finite binary value set, including subnormals and zero. Redundant
mantissa/exponent representations denote the same real value. -/
def Representable (F : Format) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ), F.emin - F.fractionBits ≤ e ∧
    e ≤ F.emax - F.fractionBits ∧ |(m : ℝ)| < (2 : ℝ) ^ F.precision ∧
    x = (m : ℝ) * (2 : ℝ) ^ e

theorem unitRoundoff_pos (F : Format) : 0 < F.unitRoundoff := by
  unfold unitRoundoff
  positivity

theorem quantum_pos (F : Format) (x : ℝ) : 0 < F.quantum x := by
  unfold quantum
  positivity

theorem overflowThreshold_pos (F : Format) : 0 < F.overflowThreshold := by
  have hp : (1 : ℝ) ≤ 2 ^ (F.fractionBits + 1) := one_le_pow₀ (by norm_num)
  unfold overflowThreshold
  exact mul_pos (by linarith) (by positivity)

@[simp] theorem roundFinite_zero (F : Format) : F.roundFinite 0 = 0 := by
  simp [roundFinite]

@[simp] theorem round?_zero (F : Format) : F.round? 0 = some 0 := by
  simp [round?, F.overflowThreshold_pos]

/-- Half-ulp absolute error holds even for subnormal results. -/
theorem roundFinite_abs_error (F : Format) (x : ℝ) :
    |F.roundFinite x - x| ≤ F.quantum x / 2 :=
  scaled_roundEven_error x _ (F.quantum_pos x)

theorem quantumExponent_of_normal (F : Format) {x : ℝ}
    (hx : F.minNormal ≤ |x|) :
    F.quantumExponent x = Int.log 2 |x| - F.fractionBits := by
  have hp : 0 < (2 : ℝ) ^ F.emin := by positivity
  have hl : F.emin ≤ Int.log 2 |x| :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) (hp.trans_le hx)).mp hx
  exact congrArg (fun e : ℤ => e - F.fractionBits) (max_eq_right hl)

/-- The usual unit roundoff is derived from the actual binary spacing. -/
theorem half_quantum_le_relative (F : Format) {x : ℝ}
    (hx : F.minNormal ≤ |x|) : F.quantum x / 2 ≤ F.unitRoundoff * |x| := by
  have hp : 0 < |x| := (show 0 < F.minNormal by unfold minNormal; positivity).trans_le hx
  have hl : (2 : ℝ) ^ Int.log 2 |x| ≤ |x| :=
    Int.zpow_log_le_self (by norm_num) hp
  have he : F.quantum x / 2 = F.unitRoundoff * (2 : ℝ) ^ Int.log 2 |x| := by
    unfold quantum unitRoundoff
    rw [F.quantumExponent_of_normal hx]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_one, zpow_neg, zpow_natCast]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hl F.unitRoundoff_pos.le

/-- A genuine consequence of ties-to-even rounding, not an assumed FP axiom. -/
theorem roundFinite_relativeError (F : Format) {x : ℝ} (hx : F.Safe x) :
    FP.RelativeError F.unitRoundoff x (F.roundFinite x) := by
  apply FP.relativeError_of_abs F.unitRoundoff_pos.le
  rcases hx with rfl | ⟨hn, _⟩
  · simp
  · exact (F.roundFinite_abs_error x).trans (F.half_quantum_le_relative hn)

theorem round?_eq_of_safe (F : Format) {x : ℝ} (hx : F.Safe x) :
    F.round? x = some (F.roundFinite x) := by
  rcases hx with rfl | ⟨_, hb⟩
  · simp
  · simp [round?, hb]

@[simp] theorem binary32_precision : binary32.precision = 24 := rfl
@[simp] theorem binary64_precision : binary64.precision = 53 := rfl
@[simp] theorem binary32_unitRoundoff : binary32.unitRoundoff = (2 : ℝ) ^ (-24 : ℤ) := rfl
@[simp] theorem binary64_unitRoundoff : binary64.unitRoundoff = (2 : ℝ) ^ (-53 : ℤ) := rfl

end Format
end FP.IEEE
