import FP.Compensation

/-! Input-magnitude bounds for compensated summation, including absolute error. -/
noncomputable section
namespace FP

/-- The exact high-prefix error and residual mass admit a joint input-based bound. -/
theorem compensation_input_mass_step {u ε T A s M a s' e : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hT : |T| ≤ A) (hh : |s-T| ≤ M)
    (hM : M ≤ growth u n*A+ε*geomWeight u n)
    (he : s+a = s'+e) (hs : MixedError u ε (s+a) s') :
    |T+a| ≤ A+|a| ∧ |s'-(T+a)| ≤ M+|e| ∧
      M+|e| ≤ growth u (n+1)*(A+|a|)+ε*geomWeight u (n+1) := by
  have htot : |T+a| ≤ A+|a| := (abs_add_le T a).trans (add_le_add hT le_rfl)
  have hhigh : |s'-(T+a)| ≤ M+|e| := by
    have ht : |s-T-e| ≤ |s-T|+|e| := by simpa [sub_eq_add_neg] using abs_add_le (s-T) (-e)
    rw [show s-T-e = s'-(T+a) by linarith] at ht
    exact ht.trans (add_le_add hh le_rfl)
  have hsa : |s+a| ≤ M+A+|a| := by
    have ht := abs_add_le (s-T) (T+a)
    rw [show s-T+(T+a) = s+a by ring] at ht
    linarith
  have he' : |e| ≤ u*(M+A+|a|)+ε := by
    have hres : |e| ≤ u*|s+a|+ε := by
      simpa [MixedError, show s'-(s+a) = -e by linarith] using hs
    exact hres.trans (add_le_add (mul_le_mul_of_nonneg_left hsa hu) le_rfl)
  have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ 1+u by linarith)
  have hg := growth_nonneg hu n
  have hga := mul_nonneg (mul_nonneg (show 0 ≤ 1+u by linarith) hg) (abs_nonneg a)
  have hn : growth u (n+1) = (1+u)*growth u n+u := by simp [growth, pow_succ]; ring
  refine ⟨htot,hhigh,?_⟩
  rw [hn,geomWeight_succ]
  nlinarith

/-- Eliminating the residual mass gives a second-order input-magnitude bound. -/
theorem compensation_input_bound {u ε S A M E : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hM : M ≤ growth u n*A+ε*geomWeight u n)
    (hE : E ≤ u*|S|+(1+u)*(growth u n*M+ε*geomWeight u n)+ε) :
    E ≤ u*|S|+(1+u)*((growth u n)^2*A+ε*(1+growth u n)*geomWeight u n)+ε := by
  have hm := mul_le_mul_of_nonneg_left hM (growth_nonneg hu n)
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1+u by linarith)
  nlinarith

/-- Geometric accumulation and growth coincide after multiplication by unit roundoff. -/
theorem mul_geomWeight_eq_growth (u : ℝ) (n : ℕ) : u*geomWeight u n = growth u n := by
  induction n with
  | zero => simp [growth]
  | succ n ih =>
    rw [geomWeight_succ]
    have hn : growth u (n+1) = (1+u)*growth u n+u := by simp [growth,pow_succ]; ring
    rw [hn,← ih]
    ring

theorem geomWeight_le_gamma_den {u : ℝ} (hu : 0 < u) (n : ℕ) (hn : n*u < 1) :
    geomWeight u n ≤ (n : ℝ)/(1-n*u) := by
  have hg := growth_le_gamma hu.le n hn
  have hd : 0 < 1-(n : ℝ)*u := by linarith
  have he : geomWeight u n = growth u n/u := by
    apply (eq_div_iff (ne_of_gt hu)).mpr
    simpa [mul_comm] using mul_geomWeight_eq_growth u n
  rw [he]
  calc
    growth u n/u ≤ gamma u n/u := div_le_div_of_nonneg_right hg hu.le
    _ = (n : ℝ)/(1-n*u) := by unfold gamma; field_simp

/-- Closed gamma form, with the absolute underflow contribution retained. -/
theorem compensation_input_gamma_bound {u ε S A E : ℝ} {n : ℕ}
    (hu : 0 < u) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hn : n*u < 1)
    (hE : E ≤ u*|S|+(1+u)*((growth u n)^2*A+ε*(1+growth u n)*geomWeight u n)+ε) :
    E ≤ u*|S|+(1+u)*((gamma u n)^2*A+(n : ℝ)*ε/(1-n*u)^2)+ε := by
  have hg0 := growth_nonneg hu.le n
  have hg := growth_le_gamma hu.le n hn
  have hγ0 : 0 ≤ gamma u n := hg0.trans hg
  have hd : 0 < 1-(n : ℝ)*u := by linarith
  have hG := geomWeight_le_gamma_den hu n hn
  have hs : (growth u n)^2*A ≤ (gamma u n)^2*A := by
    apply mul_le_mul_of_nonneg_right _ hA
    nlinarith
  have hfirst : ε*(1+growth u n) ≤ ε*(1+gamma u n) :=
    mul_le_mul_of_nonneg_left (by linarith) hε
  have ht := mul_le_mul hfirst hG (geomWeight_nonneg hu.le n)
    (mul_nonneg hε (by linarith : 0 ≤ 1+gamma u n))
  have he : ε*(1+gamma u n)*((n : ℝ)/(1-n*u)) = (n : ℝ)*ε/(1-n*u)^2 := by
    unfold gamma
    field_simp
    ring
  rw [he] at ht
  have hh := mul_le_mul_of_nonneg_left (add_le_add hs ht) (show 0 ≤ 1+u by linarith)
  linarith

/-- Traditional-model specialization: second order in unit roundoff beyond the
unavoidable final-rounding term. -/
theorem compensation_input_relative_bound {u S A M E : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hM : M ≤ growth u n*A)
    (hE : E ≤ u*|S|+(1+u)*growth u n*M) :
    E ≤ u*|S|+(1+u)*(growth u n)^2*A := by
  have hh := compensation_input_bound (ε := 0) hu (by simpa using hM) (by simpa [mul_assoc] using hE)
  simpa [mul_assoc] using hh

end FP
