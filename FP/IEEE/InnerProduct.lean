import FP.IEEE.Format
import FP.InnerProduct

/-! Backward stability for the finite-value semantics of IEEE binary32/binary64. -/
noncomputable section
namespace FP.IEEE
open scoped BigOperators

namespace Format

/-- IEEE sequential dot product. `none` propagates overflow; multiplication and
addition each round separately. Inputs are exact real values of finite operands. -/
def dot? (F : Format) (x y : ℕ → ℝ) : ℕ → Option ℝ
  | 0 => some 0
  | n + 1 => do
    let s ← F.dot? x y n
    let p ← F.round? (x n * y n)
    F.round? (s + p)

/-- Local range obligations for the exact products and pre-rounded sums. -/
def SafeDot (F : Format) (x y : ℕ → ℝ) (n : ℕ) : Prop :=
  FP.SafeTrace F.Safe F.roundFinite x y n

theorem dot?_eq_of_safe (F : Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : F.SafeDot x y n) :
    F.dot? x y n = some (FP.roundedDot F.roundFinite x y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun i hi => hs i (by omega))
    simp only [dot?, hn, F.round?_eq_of_safe (hs n (by omega)).1,
      FP.roundedDot]
    exact F.round?_eq_of_safe (hs n (by omega)).2

/-- No operation-error hypotheses: they are proved from the specified binary
rounding function. The trace assumptions contain only range conditions. -/
theorem innerProduct_backward (F : Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : F.SafeDot x y n) (hn : (2 * n : ℕ) * F.unitRoundoff < 1) :
    ∃ s : ℝ, F.dot? x y n = some s ∧
      FP.BackwardStable (FP.gamma F.unitRoundoff (2 * n)) x y n s := by
  refine ⟨FP.roundedDot F.roundFinite x y n, F.dot?_eq_of_safe x y n hs, ?_⟩
  exact (FP.roundedDot_backward F.unitRoundoff F.unitRoundoff_pos.le
    F.roundFinite F.Safe (fun _ hx => F.roundFinite_relativeError hx)
    x y n hs).mono (FP.growth_le_gamma F.unitRoundoff_pos.le _ hn)

end Format

theorem binary32_innerProduct_backward (x y : ℕ → ℝ) (n : ℕ)
    (hs : binary32.SafeDot x y n) (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-24 : ℤ) < 1) :
    ∃ s : ℝ, binary32.dot? x y n = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-24 : ℤ)) (2 * n)) x y n s :=
  binary32.innerProduct_backward x y n hs hn

theorem binary64_innerProduct_backward (x y : ℕ → ℝ) (n : ℕ)
    (hs : binary64.SafeDot x y n) (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-53 : ℤ) < 1) :
    ∃ s : ℝ, binary64.dot? x y n = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-53 : ℤ)) (2 * n)) x y n s :=
  binary64.innerProduct_backward x y n hs hn

end FP.IEEE
