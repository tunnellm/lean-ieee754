import FP.MixedError

/-! Error accounting for a high accumulator plus a rounded correction accumulator.
The correction bound depends on the mass of the recovered low parts. -/
namespace FP
noncomputable section

structure CompensationInvariant (u ε total high correction radius mass highMass : ℝ) (n : ℕ) : Prop where
  radius_nonneg : 0 ≤ radius
  mass_nonneg : 0 ≤ mass
  error : |high+correction-total| ≤ radius
  correction_mag : |correction| ≤ mass+radius
  radius_bound : radius ≤ growth u n * mass + ε * geomWeight u n
  mass_bound : mass ≤ u*highMass + n*ε

theorem compensation_zero (u ε : ℝ) : CompensationInvariant u ε 0 0 0 0 0 0 0 := by
  constructor <;> simp [growth]

/-- The exact low part transfers the high-addition error into the correction channel. -/
theorem compensation_step {u ε T s c R M H a s' e c' : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (_hε : 0 ≤ ε) (h : CompensationInvariant u ε T s c R M H n)
    (he : s+a = s'+e) (hs : MixedError u ε (s+a) s') (hc : MixedError u ε (c+e) c') :
    CompensationInvariant u ε (T+a) s' c' (R+|c'-(c+e)|) (M+|e|) (H+|s+a|) (n+1) := by
  have herr : |s'+c'-(T+a)| ≤ R+|c'-(c+e)| := by
    calc
      _ = |(s+c-T)+(c'-(c+e))| := by congr 1; linarith
      _ ≤ |s+c-T|+|c'-(c+e)| := abs_add_le _ _
      _ ≤ _ := add_le_add h.error le_rfl
  have hmag : |c+e| ≤ M+R+|e| := (abs_add_le c e).trans (add_le_add h.correction_mag le_rfl)
  have hcmag : |c'| ≤ (M+|e|)+(R+|c'-(c+e)|) := by
    have ht := abs_add_le (c'-(c+e)) (c+e)
    rw [sub_add_cancel] at ht
    linarith
  have hres : |e| ≤ u*|s+a|+ε := by
    have he' : s'-(s+a) = -e := by linarith
    simpa [MixedError, he'] using hs
  have hg : 0 ≤ growth u n := growth_nonneg hu n
  have hn : growth u (n+1) = (1+u)*growth u n+u := by
    simp [growth, pow_succ]; ring
  have hrad : R+|c'-(c+e)| ≤ growth u (n+1)*(M+|e|)+ε*geomWeight u (n+1) := by
    have hc' : |c'-(c+e)| ≤ u*(M+R+|e|)+ε :=
      hc.trans (add_le_add (mul_le_mul_of_nonneg_left hmag hu) le_rfl)
    have hR := mul_le_mul_of_nonneg_left h.radius_bound (show 0 ≤ 1+u by linarith)
    have ht := mul_nonneg (mul_nonneg (show 0 ≤ 1+u by linarith) hg) (abs_nonneg e)
    rw [hn, geomWeight_succ]
    nlinarith
  constructor
  · exact add_nonneg h.radius_nonneg (abs_nonneg _)
  · exact add_nonneg h.mass_nonneg (abs_nonneg _)
  · exact herr
  · exact hcmag
  · exact hrad
  · push_cast
    linarith [h.mass_bound]

/-- Final rounding has a first-order contribution; the correction contribution
is bounded by the accumulated low-part error. -/
theorem compensation_finish {u ε T s c R M H r : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : CompensationInvariant u ε T s c R M H n)
    (hr : MixedError u ε (s+c) r) :
    |r-T| ≤ u*|T|+(1+u)*R+ε := by
  have hm : |s+c| ≤ R+|T| := by
    have ht := abs_add_le (s+c-T) T
    rw [sub_add_cancel] at ht
    linarith [h.error]
  have ht := abs_add_le (r-(s+c)) (s+c-T)
  rw [sub_add_sub_cancel] at ht
  have hh := mul_le_mul_of_nonneg_left hm hu
  dsimp [MixedError] at hr
  nlinarith [h.error]

/-- The error beyond final rounding is proportional to recovered residual mass. -/
theorem compensation_residual_bound {u ε T s c R M H r : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : CompensationInvariant u ε T s c R M H n)
    (hr : MixedError u ε (s+c) r) :
    |r-T| ≤ u*|T|+(1+u)*(growth u n*M+ε*geomWeight u n)+ε := by
  have hh := mul_le_mul_of_nonneg_left h.radius_bound (show 0 ≤ 1+u by linarith)
  linarith [compensation_finish hu h hr]

/-- Substituting the high-addition residual bounds exposes the second-order term.
No smallness condition on n*u is required; epsilon allows gradual underflow. -/
theorem compensation_second_order {u ε T s c R M H r : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : CompensationInvariant u ε T s c R M H n)
    (hr : MixedError u ε (s+c) r) :
    |r-T| ≤ u*|T|+(1+u)*(growth u n*(u*H+n*ε)+ε*geomWeight u n)+ε := by
  have hm := mul_le_mul_of_nonneg_left h.mass_bound (growth_nonneg hu n)
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+u by linarith)
  linarith [compensation_residual_bound hu h hr]
/-- Conventional gamma version when n*u is small enough. -/
theorem compensation_second_order_gamma {u ε T s c R M H r : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hn : n*u < 1) (h : CompensationInvariant u ε T s c R M H n)
    (hr : MixedError u ε (s+c) r) :
    |r-T| ≤ u*|T|+(1+u)*(gamma u n*(u*H+n*ε)+ε*geomWeight u n)+ε := by
  have hp : 0 ≤ u*H+n*ε := h.mass_nonneg.trans h.mass_bound
  have hg := mul_le_mul_of_nonneg_right (growth_le_gamma hu n hn) hp
  have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1+u by linarith)
  linarith [compensation_second_order hu h hr]

/-- Traditional relative-error model specialization (no absolute underflow term). -/
theorem compensation_relative_bound {u T s c R M H r : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : CompensationInvariant u 0 T s c R M H n)
    (hr : RelativeError u (s+c) r) :
    |r-T| ≤ u*|T|+(1+u)*growth u n*u*H := by
  have hm := (mixedError_zero_iff hu).mpr hr
  have hb := compensation_second_order hu h hm
  simpa [mul_assoc] using hb
end
end FP
