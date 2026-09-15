import FP.MixedError
import FP.InnerProduct

noncomputable section
namespace FP
open scoped BigOperators

/-- Relative perturbation of the first vector, plus a bounded absolute residual. -/
def MixedBackwardStable (β B : ℝ) (x y : ℕ → ℝ) (n : ℕ) (s : ℝ) : Prop :=
  ∃ x' : ℕ → ℝ, ∃ ρ : ℝ, s = (∑ i ∈ Finset.range n, x' i * y i) + ρ ∧
    (∀ i < n, |x' i - x i| ≤ β * |x i|) ∧ |ρ| ≤ B

theorem mixedBackwardStable_zero_iff (β : ℝ) (x y : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    MixedBackwardStable β 0 x y n s ↔ BackwardStable β x y n s := by
  constructor
  · rintro ⟨x', ρ, hs, hx, hρ⟩
    have hz : ρ = 0 := abs_nonpos_iff.mp hρ
    exact ⟨x', by simpa [hz] using hs, hx⟩
  · rintro ⟨x', hs, hx⟩
    exact ⟨x', 0, by simpa using hs, hx, by simp⟩

def dotMass (x y : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, |x i * y i|

theorem dotMass_nonneg (x y : ℕ → ℝ) (n : ℕ) : 0 ≤ dotMass x y n :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private def direction (z : ℝ) : ℝ := if z < 0 then -1 else 1
private theorem direction_abs (z : ℝ) : |direction z| = 1 := by
  unfold direction; split_ifs <;> norm_num
private theorem mul_direction (z : ℝ) : z * direction z = |z| := by
  unfold direction; split_ifs with hz
  · simp [abs_of_neg hz]
  · simp [abs_of_nonneg (le_of_not_gt hz)]

/-- For a scalar dot product, a mixed forward bound admits a componentwise
backward explanation. The residual carries error not explainable relatively. -/
theorem mixedBackwardStable_of_abs {β B : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (x y : ℕ → ℝ) (n : ℕ) (s : ℝ)
    (hs : |s - ∑ i ∈ Finset.range n, x i * y i| ≤ β * dotMass x y n + B) :
    MixedBackwardStable β B x y n s := by
  let a := dotMass x y n
  let d := s - ∑ i ∈ Finset.range n, x i * y i
  have he : MixedError β B a (a + d) := by
    simpa [MixedError, a, d, abs_of_nonneg (dotMass_nonneg x y n)] using hs
  obtain ⟨δ, ρ, hδ, hρ, hv⟩ := (mixedError_decomposition hβ hB).mp he
  let x' : ℕ → ℝ := fun i => x i * (1 + δ * direction (x i * y i))
  refine ⟨x', ρ, ?_, ?_, hρ⟩
  · have hi : ∀ i, x' i * y i = x i * y i + δ * |x i * y i| := by
      intro i
      dsimp [x']
      rw [← mul_direction]
      ring
    simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [a, d] at hv
    unfold dotMass at hv
    linarith
  · intro i _
    have hi : x' i - x i = x i * δ * direction (x i * y i) := by dsimp [x']; ring
    rw [hi, abs_mul, abs_mul, direction_abs, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (x i))]

theorem MixedBackwardStable.forward {β B : ℝ} {x y : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (h : MixedBackwardStable β B x y n s) :
    |s - ∑ i ∈ Finset.range n, x i * y i| ≤ β * dotMass x y n + B := by
  obtain ⟨x', ρ, hs, hx, hρ⟩ := h
  have he : |∑ i ∈ Finset.range n, (x' i - x i) * y i| ≤ β * dotMass x y n := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, |(x' i - x i) * y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, β * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [abs_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right (hx i (Finset.mem_range.mp hi)) (abs_nonneg (y i))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hv : s - ∑ i ∈ Finset.range n, x i * y i =
      (∑ i ∈ Finset.range n, (x' i - x i) * y i) + ρ := by
    rw [hs]
    simp [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hv]
  exact (abs_add_le _ _).trans (add_le_add he hρ)

theorem MixedBackwardStable.mono {β B β' B' : ℝ} {x y : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (h : MixedBackwardStable β B x y n s) (hβ : β ≤ β') (hB : B ≤ B') :
    MixedBackwardStable β' B' x y n s := by
  obtain ⟨x', ρ, hs, hx, hρ⟩ := h
  exact ⟨x', ρ, hs, fun i hi => (hx i hi).trans
    (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)), hρ.trans hB⟩

/-- Absolute residual budget for separate product and accumulator roundings. -/
def dotResidual (u ε : ℝ) (n : ℕ) : ℝ := ε * (2 + u) * geomWeight u n

theorem dotResidual_nonneg {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ dotResidual u ε n := by
  unfold dotResidual
  exact mul_nonneg (mul_nonneg hε (by linarith)) (geomWeight_nonneg hu n)

theorem roundedDot_mixed_error {u ε : ℝ} (hu : 0 ≤ u) (_hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x y : ℕ → ℝ) (n : ℕ) (hs : SafeTrace P r x y n) :
    |roundedDot r x y n - ∑ i ∈ Finset.range n, x i * y i| ≤
      growth u (2 * n) * dotMass x y n + dotResidual u ε n := by
  induction n with
  | zero => simp [roundedDot, dotMass, dotResidual]
  | succ n ih =>
    have hn := ih (fun i hi => hs i (by omega))
    have hp := hr _ (hs n (by omega)).1
    have ha := hr _ (hs n (by omega)).2
    have he := MixedError.add hu hn hp ha
    have hmag : |(∑ i ∈ Finset.range n, x i * y i) + x n * y n| ≤
        dotMass x y n + |x n * y n| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
    have hm := dotMass_nonneg x y n
    have hg1 := growth_mono hu (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
    have hg2 := growth_mono hu (show 2 ≤ 2 * (n + 1) by omega)
    have hid : growth u (2 * n + 1) = (1 + u) * growth u (2 * n) + u := by
      simp [growth, pow_succ]; ring
    have hid2 : growth u 2 = (1 + u) * u + u := by simp [growth]; ring
    rw [hid] at hg1
    rw [hid2] at hg2
    have hb1 := mul_le_mul_of_nonneg_right hg1 hm
    have hb2 := mul_le_mul_of_nonneg_right hg2 (abs_nonneg (x n * y n))
    have hres : dotResidual u ε (n + 1) = (1 + u) * dotResidual u ε n + (1 + u) * ε + ε := by
      rw [dotResidual, geomWeight_succ, dotResidual]
      ring
    simp only [roundedDot, Finset.sum_range_succ]
    rw [show dotMass x y (n + 1) = dotMass x y n + |x n * y n| by
      simp [dotMass, Finset.sum_range_succ], hres]
    nlinarith [mul_le_mul_of_nonneg_left hmag hu]

theorem roundedDot_mixed_backward {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x y : ℕ → ℝ) (n : ℕ) (hs : SafeTrace P r x y n) :
    MixedBackwardStable (growth u (2 * n)) (dotResidual u ε n) x y n (roundedDot r x y n) :=
  mixedBackwardStable_of_abs (growth_nonneg hu _) (dotResidual_nonneg hu hε _)
    x y n _ (roundedDot_mixed_error hu hε r P hr x y n hs)

end FP
