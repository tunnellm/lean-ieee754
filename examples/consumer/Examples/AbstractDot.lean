import FP.InnerProduct

/-! Reuse the traditional model for an arbitrary rounding function. -/
namespace Examples

theorem abstract_dot_backward (u : ℝ) (hu : 0 ≤ u)
    (round : ℝ → ℝ) (hr : ∀ z, FP.RelativeError u z (round z))
    (x y : ℕ → ℝ) (n : ℕ) (hn : (2 * n : ℕ) * u < 1) :
    FP.BackwardStable (FP.gamma u (2 * n)) x y n (FP.roundedDot round x y n) :=
  FP.traditional_innerProduct_backward u hu round hr x y n hn

end Examples
