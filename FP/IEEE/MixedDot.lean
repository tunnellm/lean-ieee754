import FP.IEEE.InnerProduct
import FP.IEEE.Representation
import FP.MixedBackward

noncomputable section
namespace FP.IEEE.Format

theorem dot?_eq_of_nonoverflow (F : Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : FP.SafeTrace (fun z => |z| < F.overflowThreshold) F.roundFinite x y n) :
    F.dot? x y n = some (FP.roundedDot F.roundFinite x y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun i hi => hs i (by omega))
    simp only [dot?, hn, round?, if_pos (hs n (by omega)).1]
    change F.round? (FP.roundedDot F.roundFinite x y n + F.roundFinite (x n * y n)) = _
    rw [round?, if_pos (hs n (by omega)).2]
    rfl

theorem dot?_mixed_backward (F : Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : FP.SafeTrace (fun z => |z| < F.overflowThreshold) F.roundFinite x y n) :
    ∃ s : ℝ, F.dot? x y n = some s ∧
      FP.MixedBackwardStable (FP.growth F.unitRoundoff (2 * n))
        (FP.dotResidual F.unitRoundoff (F.minSubnormal / 2) n) x y n s := by
  refine ⟨FP.roundedDot F.roundFinite x y n, F.dot?_eq_of_nonoverflow x y n hs, ?_⟩
  exact FP.roundedDot_mixed_backward F.unitRoundoff_pos.le
    (by unfold minSubnormal; positivity) F.roundFinite _
    (fun z _ => F.roundFinite_mixed_error z) x y n hs

theorem dot?_mixed_backward_gamma (F : Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : FP.SafeTrace (fun z => |z| < F.overflowThreshold) F.roundFinite x y n)
    (hn : (2 * n : ℕ) * F.unitRoundoff < 1) :
    ∃ s : ℝ, F.dot? x y n = some s ∧
      FP.MixedBackwardStable (FP.gamma F.unitRoundoff (2 * n))
        (FP.dotResidual F.unitRoundoff (F.minSubnormal / 2) n) x y n s := by
  obtain ⟨s, hv, he⟩ := F.dot?_mixed_backward x y n hs
  exact ⟨s, hv, he.mono (FP.growth_le_gamma F.unitRoundoff_pos.le _ hn) le_rfl⟩

end FP.IEEE.Format
