import FP.Range.Compensated

/-! Uniform rational accuracy bounds for whole input domains. -/
namespace FP.Range
open scoped BigOperators

theorem exactSumInterval_sound {bounds : List Interval} {xs : List ℝ}
    (h : List.Forall₂ Interval.Contains bounds xs) :
    (exactSumInterval bounds).Contains xs.sum ∧
      (xs.map (fun x => |x|)).sum ≤ (sumIntervalMass bounds : ℝ) := by
  induction h with
  | nil => exact ⟨Interval.contains_zero,by simp [sumIntervalMass]⟩
  | @cons b x bs xs hx h ih =>
    refine ⟨by simpa [exactSumInterval] using Interval.contains_add hx ih.1,?_⟩
    simpa [sumIntervalMass] using add_le_add (Interval.abs_le_radius hx) ih.2

theorem exactDotInterval_sound (A B : ℕ → Interval) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, (A i).Contains (x i)) (hy : ∀ i < n, (B i).Contains (y i)) :
    (exactDotInterval A B n).Contains (∑ i ∈ Finset.range n, x i*y i) ∧
      (∑ i ∈ Finset.range n, |x i*y i|) ≤ (dotIntervalMass A B n : ℝ) := by
  induction n with
  | zero => simpa [exactDotInterval,dotIntervalMass] using And.intro Interval.contains_zero (le_refl (0 : ℝ))
  | succ n ih =>
    obtain ⟨ht,hm⟩ := ih (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    have hp := Interval.contains_mul (hx n (by omega)) (hy n (by omega))
    exact ⟨by simpa [exactDotInterval,Finset.sum_range_succ] using Interval.contains_add ht hp,
      by simpa [dotIntervalMass,Finset.sum_range_succ] using add_le_add hm (Interval.abs_le_radius hp)⟩

theorem sumAccuracyBound_sound (F : IEEE.Format) (T : Interval) (M : ℚ) (S A E : ℝ) (n : ℕ)
    (hT : T.Contains S) (hM : A ≤ (M : ℝ))
    (hE : E ≤ F.unitRoundoff*|S|+(1+F.unitRoundoff)*
      ((growth F.unitRoundoff n)^2*A+(F.minSubnormal/2)*
        (1+growth F.unitRoundoff n)*geomWeight F.unitRoundoff n)+F.minSubnormal/2) :
    E ≤ (sumAccuracyBound (.ofFormat F) T M n : ℝ) := by
  have hS := mul_le_mul_of_nonneg_left (Interval.abs_le_radius hT) F.unitRoundoff_pos.le
  have hA := mul_le_mul_of_nonneg_left hM (sq_nonneg (growth F.unitRoundoff n))
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ 1+F.unitRoundoff by linarith [F.unitRoundoff_pos])
  simp only [sumAccuracyBound,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_one,
    growthRat_cast,geomWeightRat_cast,Params.ofFormat_u,Params.ofFormat_ε]
  linarith

theorem dotAccuracyBound_sound (F : IEEE.Format) (T : Interval) (M : ℚ) (S A E : ℝ) (n : ℕ)
    (hT : T.Contains S) (hM : A ≤ (M : ℝ))
    (hE : E ≤ F.unitRoundoff*|S|+(1+F.unitRoundoff)*
      ((growth F.unitRoundoff (2*n))^2*A+(F.minSubnormal/2)*
        (1+growth F.unitRoundoff (2*n))*(geomWeight F.unitRoundoff (2*n)+n))+F.minSubnormal/2) :
    E ≤ (dotAccuracyBound (.ofFormat F) T M n : ℝ) := by
  have hS := mul_le_mul_of_nonneg_left (Interval.abs_le_radius hT) F.unitRoundoff_pos.le
  have hA := mul_le_mul_of_nonneg_left hM (sq_nonneg (growth F.unitRoundoff (2*n)))
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ 1+F.unitRoundoff by linarith [F.unitRoundoff_pos])
  simp only [dotAccuracyBound,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_one,Rat.cast_natCast,
    growthRat_cast,geomWeightRat_cast,Params.ofFormat_u,Params.ofFormat_ε]
  linarith

end FP.Range
