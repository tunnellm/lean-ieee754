import FP.IEEE.WordInnerProduct

/-! Boundary results explain why the range hypotheses are necessary. -/
noncomputable section
namespace FP.IEEE
namespace Format

theorem minNormal_le_overflowThreshold (F : Format) : F.minNormal ≤ F.overflowThreshold := by
  have hp : (1 : ℝ) ≤ 2 ^ F.fractionBits := one_le_pow₀ (by norm_num)
  have he : (2 : ℝ) ^ F.fractionBits * (2 : ℝ) ^ (F.emax - F.fractionBits) =
      (2 : ℝ) ^ F.emax := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hscale : 0 < (2 : ℝ) ^ (F.emax - F.fractionBits) := by positivity
  calc
    F.minNormal ≤ (2 : ℝ) ^ F.emax :=
      zpow_le_zpow_right₀ (by norm_num) F.exponent_order
    _ ≤ F.overflowThreshold := by
      unfold overflowThreshold
      rw [pow_succ, ← he]
      nlinarith

theorem minSubnormal_le_minNormal (F : Format) : F.minSubnormal ≤ F.minNormal := by
  exact zpow_le_zpow_right₀ (by norm_num) (by omega : F.emin - F.fractionBits ≤ F.emin)

theorem half_minSubnormal_eq (F : Format) :
    F.minSubnormal / 2 = (2 : ℝ) ^ (F.emin - F.fractionBits - 1) := by
  simp [minSubnormal, zpow_sub₀]

/-- The midpoint between zero and the least positive subnormal ties to zero. -/
theorem roundFinite_half_minSubnormal (F : Format) :
    F.roundFinite (F.minSubnormal / 2) = 0 := by
  have hp : 0 < F.minSubnormal := by unfold minSubnormal; positivity
  have hq : F.quantum (F.minSubnormal / 2) = F.minSubnormal := by
    unfold quantum quantumExponent
    have hl := Int.log_zpow (R := ℝ) (by norm_num : 1 < (2 : ℕ))
      (F.emin - F.fractionBits - 1)
    norm_num only [Nat.cast_ofNat] at hl
    rw [abs_of_pos (by positivity), F.half_minSubnormal_eq, hl, max_eq_left (by omega)]
    rfl
  have hr : roundEven (1 / 2 : ℝ) = 0 := by
    simpa using roundEven_midpoint 0
  unfold roundFinite
  rw [hq]
  have he : F.minSubnormal / 2 / F.minSubnormal = 1 / 2 := by field_simp
  rw [he, hr]
  simp

theorem round?_half_minSubnormal (F : Format) :
    F.round? (F.minSubnormal / 2) = some 0 := by
  have hp : 0 < F.minSubnormal := by unfold minSubnormal; positivity
  have hlt : |F.minSubnormal / 2| < F.overflowThreshold := by
    rw [abs_of_pos (by positivity)]
    have hle := F.minSubnormal_le_minNormal.trans F.minNormal_le_overflowThreshold
    linarith
  simp [round?, hlt, F.roundFinite_half_minSubnormal]

/-- A one-term product of the least subnormal and one-half underflows to zero. -/
theorem underflow_dot (F : Format) :
    F.dot? (fun _ => F.minSubnormal) (fun _ => 1 / 2) 1 = some 0 := by
  simp only [dot?, mul_one_div, F.round?_half_minSubnormal]
  change F.round? ((0 : ℝ) + 0) = some 0
  simp

/-- Consequently, no relative componentwise perturbation smaller than 100%
can explain this computed one-term inner product. -/
theorem underflow_not_backwardStable (F : Format) {ε : ℝ} (hε : ε < 1) :
    ¬ FP.BackwardStable ε (fun _ => F.minSubnormal) (fun _ => 1 / 2) 1 0 := by
  intro h
  obtain ⟨x', hs, hb⟩ := h
  have hp : 0 < F.minSubnormal := by unfold minSubnormal; positivity
  have hx : x' 0 = 0 := by simpa using hs
  have he := hb 0 (by norm_num)
  simp only [hx, zero_sub, abs_neg, abs_of_pos hp] at he
  nlinarith

/-- Overflow begins at the midpoint, including the tie itself. -/
theorem round?_at_overflowThreshold (F : Format) :
    F.round? F.overflowThreshold = none := by
  simp [round?, abs_of_pos F.overflowThreshold_pos]

end Format

-- Concrete bit-pattern checks use kernel reduction and real arithmetic.
example : fp32.decode? (0x3f800000 : BitVec 32) = some 1 := by
  change fp32.decode? (0x3f800000 : fp32.Word) = some 1
  rw [fp32.decode?_eq _ (by decide)]
  have hm : fp32.mantissa (0x3f800000 : fp32.Word) = 8388608 := by decide
  have he : fp32.scaleExponent (0x3f800000 : fp32.Word) = -23 := by decide
  have hs : fp32.negative (0x3f800000 : fp32.Word) = false := by decide
  norm_num [Interchange.value, hm, he, hs]

example : fp64.decode? (0x3ff0000000000000 : BitVec 64) = some 1 := by
  change fp64.decode? (0x3ff0000000000000 : fp64.Word) = some 1
  rw [fp64.decode?_eq _ (by decide)]
  have hm : fp64.mantissa (0x3ff0000000000000 : fp64.Word) = 4503599627370496 := by decide
  have he : fp64.scaleExponent (0x3ff0000000000000 : fp64.Word) = -52 := by decide
  have hs : fp64.negative (0x3ff0000000000000 : fp64.Word) = false := by decide
  norm_num [Interchange.value, hm, he, hs]

example : fp32.decode? (0x7f800000 : BitVec 32) = none := by
  change fp32.decode? (0x7f800000 : fp32.Word) = none
  rw [Interchange.decode?, if_neg (by decide)]

example : binary32.roundFinite (binary32.minSubnormal / 2) = 0 :=
  binary32.roundFinite_half_minSubnormal

example : binary64.roundFinite (binary64.minSubnormal / 2) = 0 :=
  binary64.roundFinite_half_minSubnormal

example : fp32.decode? (0x00000001 : BitVec 32) = some ((2 : ℝ) ^ (-149 : ℤ)) := by
  change fp32.decode? (1 : fp32.Word) = _
  rw [fp32.decode?_eq _ (by decide)]
  have hm : fp32.mantissa (1 : fp32.Word) = 1 := by decide
  have he : fp32.scaleExponent (1 : fp32.Word) = -149 := by decide
  have hs : fp32.negative (1 : fp32.Word) = false := by decide
  simp only [Interchange.value, hm, he, hs, Bool.false_eq_true, if_false, Nat.cast_one, one_mul]

example : fp64.decode? (0x0000000000000001 : BitVec 64) = some ((2 : ℝ) ^ (-1074 : ℤ)) := by
  change fp64.decode? (1 : fp64.Word) = _
  rw [fp64.decode?_eq _ (by decide)]
  have hm : fp64.mantissa (1 : fp64.Word) = 1 := by decide
  have he : fp64.scaleExponent (1 : fp64.Word) = -1074 := by decide
  have hs : fp64.negative (1 : fp64.Word) = false := by decide
  simp only [Interchange.value, hm, he, hs, Bool.false_eq_true, if_false, Nat.cast_one, one_mul]

example : roundEven ((-3 : ℝ) / 2) = -2 := by
  convert roundEven_midpoint (-2) using 1 <;> norm_num

example : roundEven ((5 : ℝ) / 2) = 2 := by
  convert roundEven_midpoint 2 using 1 <;> norm_num

/-- A concrete admissible trace, demonstrating that the range obligations can
be discharged from the format definitions. -/
example : binary32.SafeDot (fun _ => 1) (fun _ => 1) 1 := by
  have hrepr : binary32.Representable 1 := by
    refine ⟨1, 0, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [binary32, Format.precision]
  have hr : binary32.roundFinite 1 = 1 := binary32.roundFinite_exact hrepr
  have hs : binary32.Safe 1 := by
    right
    norm_num [binary32, Format.minNormal, Format.overflowThreshold]
  intro i hi
  have he : i = 0 := by omega
  subst i
  simpa [FP.roundedDot, hr] using And.intro hs hs

end FP.IEEE
