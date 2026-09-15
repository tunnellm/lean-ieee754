import FP.Basic

/-! Sequential multiply-then-add inner products (no fused multiply-add).
The accumulator starts at zero. The bound `gamma u (2*n)` is deliberately
conservative: at most two rounding operations per term.
-/
noncomputable section
namespace FP
open scoped BigOperators

def roundedDot (r : ℝ → ℝ) (x y : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => r (roundedDot r x y n + r (x n * y n))

/-- Range conditions on exact inputs to rounding, not on its errors. -/
def SafeTrace (P : ℝ → Prop) (r : ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i < n, P (x i * y i) ∧ P (roundedDot r x y i + r (x i * y i))

/-- Componentwise perturbations to the first input; the second is unchanged. -/
def BackwardStable (ε : ℝ) (x y : ℕ → ℝ) (n : ℕ) (s : ℝ) : Prop :=
  ∃ x' : ℕ → ℝ, s = ∑ i ∈ Finset.range n, x' i * y i ∧
    ∀ i < n, |x' i - x i| ≤ ε * |x i|

theorem roundedDot_weights (u : ℝ) (hu : 0 ≤ u) (r : ℝ → ℝ)
    (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x y : ℕ → ℝ) (n : ℕ) (hs : SafeTrace P r x y n) :
    ∃ w : ℕ → ℝ,
      roundedDot r x y n = ∑ i ∈ Finset.range n, x i * y i * w i ∧
      ∀ i < n, |w i - 1| ≤ growth u (2 * n) := by
  induction n with
  | zero => exact ⟨fun _ => 1, by simp [roundedDot], by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hb⟩ := ih (fun i hi => hs i (by omega))
    obtain ⟨δ, hδ, eδ⟩ := hr _ (hs n (by omega)).1
    obtain ⟨η, hη, eη⟩ := hr _ (hs n (by omega)).2
    let w' : ℕ → ℝ := fun i => if i = n then (1 + δ) * (1 + η)
      else w i * (1 + η)
    refine ⟨w', ?_, ?_⟩
    · rw [roundedDot, eη, hw, eδ, Finset.sum_range_succ]
      have hsum : (∑ i ∈ Finset.range n, x i * y i * w' i) =
          (∑ i ∈ Finset.range n, x i * y i * w i) * (1 + η) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [w', if_neg (ne_of_lt (Finset.mem_range.mp hi))]
        ring
      rw [hsum]
      simp only [w', if_pos rfl]
      ring
    · intro i hi
      by_cases hin : i = n
      · subst i
        simp only [w', if_pos rfl]
        exact (factor_bound hu (one_add_error hδ) (one_add_error hη)).trans
          (growth_mono hu (by omega))
      · simp only [w', if_neg hin]
        exact (factor_bound hu (hb i (by omega)) (one_add_error hη)).trans
          (growth_mono hu (by omega))

theorem roundedDot_backward (u : ℝ) (hu : 0 ≤ u) (r : ℝ → ℝ)
    (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x y : ℕ → ℝ) (n : ℕ) (hs : SafeTrace P r x y n) :
    BackwardStable (growth u (2 * n)) x y n (roundedDot r x y n) := by
  obtain ⟨w, hw, hb⟩ := roundedDot_weights u hu r P hr x y n hs
  refine ⟨fun i => x i * w i, ?_, ?_⟩
  · rw [hw]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i hi
    calc
      |x i * w i - x i| = |w i - 1| * |x i| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ growth u (2 * n) * |x i| :=
        mul_le_mul_of_nonneg_right (hb i hi) (abs_nonneg _)

theorem BackwardStable.mono {ε ε' : ℝ} {x y : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (h : BackwardStable ε x y n s) (he : ε ≤ ε') : BackwardStable ε' x y n s := by
  obtain ⟨x', hx', hb⟩ := h
  exact ⟨x', hx', fun i hi => (hb i hi).trans
    (mul_le_mul_of_nonneg_right he (abs_nonneg _))⟩

/-- Traditional FP model, with the conventional `gamma_(2n)` bound. -/
theorem traditional_innerProduct_backward (u : ℝ) (hu : 0 ≤ u)
    (r : ℝ → ℝ) (hr : ∀ z, RelativeError u z (r z))
    (x y : ℕ → ℝ) (n : ℕ) (hn : (2 * n : ℕ) * u < 1) :
    BackwardStable (gamma u (2 * n)) x y n (roundedDot r x y n) := by
  exact (roundedDot_backward u hu r (fun _ => True) (fun z _ => hr z)
    x y n (fun _ _ => ⟨trivial, trivial⟩)).mono (growth_le_gamma hu _ hn)

end FP
