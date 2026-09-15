import FP.CompensationInput
import FP.MixedBackward

/-! Online Dot2 accounting, with a separate budget for inexact product residuals. -/
noncomputable section
namespace FP

private theorem pair_mass_step {u ε A M a M' : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hA : 0 ≤ A) (hM0 : 0 ≤ M) (ha : 0 ≤ a)
    (hM : M ≤ growth u (2*n)*A+ε*geomWeight u (2*n))
    (hs : M' ≤ (1+u)*M+u*A+u*(2+u)*a+(2+u)*ε) :
    M' ≤ growth u (2*(n+1))*(A+a)+ε*geomWeight u (2*(n+1)) := by
  have hn : growth u (2*(n+1)) = (1+u)^2*growth u (2*n)+u*(2+u) := by
    simp [growth,show 2*(n+1)=2*n+2 by omega,pow_add]
    ring
  have hG : geomWeight u (2*(n+1)) = (1+u)^2*geomWeight u (2*n)+(2+u) := by
    rw [show 2*(n+1)=(2*n+1)+1 by omega,geomWeight_succ,geomWeight_succ]
    ring
  have hh := mul_le_mul_of_nonneg_left hM (sq_nonneg (1+u))
  have h1 := mul_nonneg (mul_nonneg hu (show 0 ≤ 1+u by linarith)) hM0
  have h2 := mul_nonneg (mul_nonneg hu (show 0 ≤ 1+u by linarith)) hA
  have h3 := mul_nonneg (mul_nonneg (sq_nonneg (1+u)) (growth_nonneg hu (2*n))) ha
  rw [hn,hG]
  nlinarith

structure DotCompensationInvariant (u ε T A s c R L M D : ℝ) (n : ℕ) : Prop where
  total_mass : |T| ≤ A
  radius_nonneg : 0 ≤ R
  loss_nonneg : 0 ≤ L
  mass_nonneg : 0 ≤ M
  defect_nonneg : 0 ≤ D
  high_error : |s-T| ≤ L
  correction_mag : |c| ≤ M+R
  error : |s+c-T| ≤ R+D
  loss_bound : L ≤ growth u (2*n)*A+ε*geomWeight u (2*n)
  mass_loss : M ≤ L+D
  radius_bound : R ≤ growth u (2*n)*M+ε*geomWeight u (2*n)
  defect_bound : D ≤ n*ε

theorem dot_compensation_zero (u ε : ℝ) : DotCompensationInvariant u ε 0 0 0 0 0 0 0 0 0 := by
  constructor <;> simp [growth]

/-- One product, one exact TwoSum split, and the two rounded correction additions. -/
theorem dot_compensation_step {u ε T A s c R L M D v p π s' σ t c' : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : DotCompensationInvariant u ε T A s c R L M D n)
    (hp : MixedError u ε v p) (he : s+p = s'+σ)
    (hs : MixedError u ε (s+p) s') (hd : |v-p-π| ≤ ε)
    (ht : MixedError u ε (π+σ) t) (hc : MixedError u ε (c+t) c') :
    DotCompensationInvariant u ε (T+v) (A+|v|) s' c'
      (R+|t-(π+σ)|+|c'-(c+t)|) (L+|v-p|+|σ|) (M+|π|+|σ|) (D+|v-p-π|) (n+1) := by
  have hA : 0 ≤ A := (abs_nonneg T).trans h.total_mass
  have hmag : |s| ≤ A+L := by
    have hh := abs_add_le (s-T) T
    rw [sub_add_cancel] at hh
    linarith [h.high_error,h.total_mass]
  have hpabs : |p| ≤ (1+u)*|v|+ε := by
    have hh := abs_add_le (p-v) v
    rw [sub_add_cancel] at hh
    dsimp [MixedError] at hp
    linarith
  have hσα : |σ| ≤ u*(A+L+(1+u)*|v|+ε)+ε := by
    have hh : |s+p| ≤ A+L+(1+u)*|v|+ε := by linarith [abs_add_le s p]
    have heq : s'-(s+p) = -σ := by linarith
    have hb : |σ| ≤ u*|s+p|+ε := by simpa [MixedError,heq] using hs
    exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left hh hu) le_rfl)
  have hL := pair_mass_step hu hA h.loss_nonneg (abs_nonneg v) h.loss_bound
    (M' := L+|v-p|+|σ|) (by dsimp [MixedError] at hp; rw [abs_sub_comm v p]; nlinarith)
  have hπ : |π| ≤ |v-p|+|v-p-π| := by
    have hh := abs_add_le (v-p) (-(v-p-π))
    rw [show v-p + -(v-p-π)=π by ring,abs_neg] at hh
    exact hh
  have htmag : |t| ≤ (1+u)*(|π|+|σ|)+ε := by
    have hh := abs_add_le (t-(π+σ)) (π+σ)
    rw [sub_add_cancel] at hh
    have hm := mul_le_mul_of_nonneg_left (abs_add_le π σ) hu
    dsimp [MixedError] at ht
    nlinarith [abs_add_le π σ]
  have htc : |c+t| ≤ M+R+(1+u)*(|π|+|σ|)+ε := by
    linarith [abs_add_le c t,h.correction_mag]
  have hte : |t-(π+σ)| ≤ u*(|π|+|σ|)+ε :=
    ht.trans (add_le_add (mul_le_mul_of_nonneg_left (abs_add_le π σ) hu) le_rfl)
  have hce : |c'-(c+t)| ≤ u*(M+R+(1+u)*(|π|+|σ|)+ε)+ε :=
    hc.trans (add_le_add (mul_le_mul_of_nonneg_left htc hu) le_rfl)
  have hR := pair_mass_step hu h.mass_nonneg h.radius_nonneg
    (add_nonneg (abs_nonneg π) (abs_nonneg σ)) h.radius_bound
    (M' := R+|t-(π+σ)|+|c'-(c+t)|) (by nlinarith)
  constructor
  · exact (abs_add_le T v).trans (add_le_add h.total_mass le_rfl)
  · exact add_nonneg (add_nonneg h.radius_nonneg (abs_nonneg _)) (abs_nonneg _)
  · exact add_nonneg (add_nonneg h.loss_nonneg (abs_nonneg _)) (abs_nonneg _)
  · exact add_nonneg (add_nonneg h.mass_nonneg (abs_nonneg _)) (abs_nonneg _)
  · exact add_nonneg h.defect_nonneg (abs_nonneg _)
  · have hh := abs_add_le (s-T) (-(v-p))
    have hj := abs_add_le ((s-T)-(v-p)) (-σ)
    have heq : (s-T)-(v-p)+ -σ = s'-(T+v) := by linarith
    rw [heq,abs_neg] at hj
    simp only [abs_neg,← sub_eq_add_neg] at hh
    linarith [h.high_error]
  · have hh := abs_add_le (c+t) (c'-(c+t))
    have hj := abs_add_le c t
    have hk := abs_add_le (π+σ) (t-(π+σ))
    rw [add_sub_cancel] at hh hk
    linarith [h.correction_mag,abs_add_le π σ]
  · have heq : s'+c'-(T+v) = (s+c-T)+(t-(π+σ))+(c'-(c+t))-(v-p-π) := by linarith
    rw [heq]
    have h1 := abs_add_le (s+c-T) (t-(π+σ))
    have h2 := abs_add_le ((s+c-T)+(t-(π+σ))) (c'-(c+t))
    have h3 := abs_sub ((s+c-T)+(t-(π+σ))+(c'-(c+t))) (v-p-π)
    linarith [h.error]
  · exact hL
  · linarith [h.mass_loss]
  · simpa [add_assoc] using hR
  · push_cast; linarith [h.defect_bound]

theorem dot_compensation_finish {u ε T A s c R L M D q : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : DotCompensationInvariant u ε T A s c R L M D n)
    (hq : MixedError u ε (s+c) q) :
    |q-T| ≤ u*|T|+(1+u)*(R+D)+ε := by
  have hm : |s+c| ≤ |T|+(R+D) := by
    have hh := abs_add_le (s+c-T) T
    rw [sub_add_cancel] at hh
    linarith [h.error]
  have ht := abs_add_le (q-(s+c)) (s+c-T)
  rw [sub_add_sub_cancel] at ht
  have hh := mul_le_mul_of_nonneg_left hm hu
  dsimp [MixedError] at hq
  nlinarith [h.error]

/-- Retain the measured product-defect mass for a sharper a posteriori bound. -/
theorem dot_compensation_defect_bound {u ε T A s c R L M D q : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : DotCompensationInvariant u ε T A s c R L M D n)
    (hq : MixedError u ε (s+c) q) :
    |q-T| ≤ u*|T|+(1+u)*((growth u (2*n))^2*A+
      (1+growth u (2*n))*(ε*geomWeight u (2*n)+D))+ε := by
  have hM : M ≤ growth u (2*n)*A+ε*geomWeight u (2*n)+D := by linarith [h.mass_loss,h.loss_bound]
  have hh := mul_le_mul_of_nonneg_left hM (growth_nonneg hu (2*n))
  have hR : R+D ≤ (growth u (2*n))^2*A+(1+growth u (2*n))*(ε*geomWeight u (2*n)+D) := by
    nlinarith [h.radius_bound]
  have hz := mul_le_mul_of_nonneg_left hR (show 0 ≤ 1+u by linarith)
  linarith [dot_compensation_finish hu h hq]

theorem dot_compensation_input_bound {u ε T A s c R L M D q : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : DotCompensationInvariant u ε T A s c R L M D n)
    (hq : MixedError u ε (s+c) q) :
    |q-T| ≤ u*|T|+(1+u)*((growth u (2*n))^2*A+
      ε*(1+growth u (2*n))*(geomWeight u (2*n)+n))+ε := by
  have hh := mul_le_mul_of_nonneg_left h.defect_bound
    (mul_nonneg (show 0 ≤ 1+u by linarith) (show 0 ≤ 1+growth u (2*n) by linarith [growth_nonneg hu (2*n)]))
  nlinarith [dot_compensation_defect_bound hu h hq]

/-- Traditional relative-error specialization; the residual reconstruction is exact. -/
theorem dot_compensation_relative_bound {u T A s c R L M D q : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (h : DotCompensationInvariant u 0 T A s c R L M D n)
    (hq : RelativeError u (s+c) q) :
    |q-T| ≤ u*|T|+(1+u)*(growth u (2*n))^2*A := by
  simpa [mul_assoc] using dot_compensation_input_bound hu h ((mixedError_zero_iff hu).mpr hq)

/-- Closed gamma bound; three absolute-error contributions per input remain. -/
theorem dot_compensation_gamma_bound {u ε T A E : ℝ} {n : ℕ}
    (hu : 0 < u) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hn : (2*n : ℕ)*u < 1)
    (hE : E ≤ u*|T|+(1+u)*((growth u (2*n))^2*A+
      ε*(1+growth u (2*n))*(geomWeight u (2*n)+n))+ε) :
    E ≤ u*|T|+(1+u)*((gamma u (2*n))^2*A+3*n*ε/(1-(2*n : ℕ)*u)^2)+ε := by
  have hd : 0 < 1-(2*n : ℕ)*u := by linarith
  have hd1 : 1-(2*n : ℕ)*u ≤ 1 := by
    have hh : 0 ≤ (2*n : ℕ)*u := mul_nonneg (by positivity) hu.le
    linarith
  have hg0 := growth_nonneg hu.le (2*n)
  have hg := growth_le_gamma hu.le (2*n) hn
  have hγ0 := hg0.trans hg
  have hs : (growth u (2*n))^2*A ≤ (gamma u (2*n))^2*A := by
    apply mul_le_mul_of_nonneg_right _ hA
    nlinarith
  have h1 : 1+growth u (2*n) ≤ 1/(1-(2*n : ℕ)*u) := by
    calc
      _ ≤ 1+gamma u (2*n) := by linarith
      _ = _ := by unfold gamma; field_simp; ring
  have hN : (n : ℝ) ≤ (n : ℝ)/(1-(2*n : ℕ)*u) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hG : geomWeight u (2*n)+(n : ℝ) ≤ 3*n/(1-(2*n : ℕ)*u) := by
    calc
      _ ≤ (2*n : ℕ)/(1-(2*n : ℕ)*u)+(n : ℝ)/(1-(2*n : ℕ)*u) :=
        add_le_add (geomWeight_le_gamma_den hu (2*n) hn) hN
      _ = _ := by push_cast; ring
  have hh := mul_le_mul h1 hG
    (add_nonneg (geomWeight_nonneg hu.le _) (by positivity)) (by positivity : (0 : ℝ) ≤ 1/(1-(2*n : ℕ)*u))
  have hhε := mul_le_mul_of_nonneg_left hh hε
  have hid : ε*(1/(1-(2*n : ℕ)*u)*(3*n/(1-(2*n : ℕ)*u))) = 3*n*ε/(1-(2*n : ℕ)*u)^2 := by field_simp
  rw [hid] at hhε
  have hc := mul_le_mul_of_nonneg_left (add_le_add hs hhε) (show 0 ≤ 1+u by linarith)
  nlinarith

end FP
