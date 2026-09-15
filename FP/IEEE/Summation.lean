import FP.Summation
import FP.IEEE.Representation

noncomputable section
namespace FP.IEEE.Format

/-- Finite-value semantics of a supplied addition schedule. -/
def sumTree? (F : Format) (x : ℕ → ℝ) : FP.ReductionTree → Option ℝ
  | .zero => some 0
  | .input i => some (x i)
  | .add l r => do
    let a ← F.sumTree? x l
    let b ← F.sumTree? x r
    F.round? (a + b)

def sequentialSum? (F : Format) (x : ℕ → ℝ) (n : ℕ) : Option ℝ :=
  F.sumTree? x (FP.sequentialTree 0 n)
def pairwiseSum? (F : Format) (x : ℕ → ℝ) (n : ℕ) : Option ℝ :=
  F.sumTree? x (FP.pairwiseTree 0 n)

theorem sumTree?_eq_of_nonoverflow (F : Format) (x : ℕ → ℝ) (t : FP.ReductionTree)
    (hs : t.Trace (fun z => |z| < F.overflowThreshold) F.roundFinite x) :
    F.sumTree? x t = some (t.rounded F.roundFinite x) := by
  induction t with
  | zero => rfl
  | input i => rfl
  | add l r hl hr =>
    simp only [sumTree?, hl hs.1, hr hs.2.1]
    change F.round? (l.rounded F.roundFinite x + r.rounded F.roundFinite x) = _
    rw [round?, if_pos hs.2.2]
    rfl

theorem sumTree_mixed_error (F : Format) (x : ℕ → ℝ) (t : FP.ReductionTree) :
    |t.rounded F.roundFinite x - t.exactSum x| ≤
      FP.growth F.unitRoundoff t.height * t.mass x +
        (F.minSubnormal / 2) * t.roundWeight F.unitRoundoff := by
  apply t.mixed_error F.unitRoundoff_pos.le (by unfold minSubnormal; positivity)
    F.roundFinite (fun _ => True) (fun z _ => F.roundFinite_mixed_error z) x
  induction t with
  | zero => trivial
  | input i => trivial
  | add l r hl hr => exact ⟨hl, hr, trivial⟩

end FP.IEEE.Format
