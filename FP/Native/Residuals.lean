import FP.Native.Accuracy
import Init.Data.Float.Model.Unpacked.Operations.Div
import Init.Data.Float.Model.Unpacked.Operations.Sqrt

/-! Exact real meanings of the residual information consumed by native division
and square root. The complete operator refinement still needs the core exponent
and packing obligations. -/
noncomputable section
namespace FP.Native
open Float.Model.UnpackedFloat

/-- Euclidean quotient/remainder determines every native fractional-accuracy case. -/
theorem quotient_represents (num den : ℕ) (hd : 0 < den) :
    Represents (ExtendedMantissa.ofMantissaAndAccuracy (num / den)
      (accuracyOfFraction (num % den) den)) ((num : ℝ) / den) := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hd
  have hrlt : ((num % den : ℕ) : ℝ) < den := by exact_mod_cast Nat.mod_lt num hd
  have hid : ((num % den : ℕ) : ℝ) + (den : ℝ) * ((num / den : ℕ) : ℝ) = num := by
    exact_mod_cast Nat.mod_add_div num den
  have hv : (num : ℝ) / den = ((num / den : ℕ) : ℝ) + ((num % den : ℕ) : ℝ) / den := by
    apply (div_eq_iff (ne_of_gt hdR)).mpr
    field_simp
    nlinarith
  have hupper : ((num % den : ℕ) : ℝ) / den < 1 := by
    exact (div_lt_one hdR).mpr hrlt
  unfold accuracyOfFraction
  split_ifs with hz
  · simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents, Bool.false_eq_true, if_false]
    rw [hv, hz]
    simp
  · have hpos : (0 : ℝ) < ((num % den : ℕ) : ℝ) / den := by
      exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hz)) hdR
    cases hc : compare (2 * (num % den)) den with
    | lt =>
      have hh : 2 * ((num % den : ℕ) : ℝ) < den := by
        exact_mod_cast (Nat.compare_eq_lt.mp hc)
      have hf : ((num % den : ℕ) : ℝ) / den < 1 / 2 := by
        apply (div_lt_iff₀ hdR).mpr; linarith
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents, Bool.false_eq_true, if_false, if_true]
      rw [hv]
      constructor <;> linarith
    | eq =>
      have hh : 2 * ((num % den : ℕ) : ℝ) = den := by
        exact_mod_cast (Nat.compare_eq_eq.mp hc)
      have hf : ((num % den : ℕ) : ℝ) / den = 1 / 2 := by
        apply (div_eq_iff (ne_of_gt hdR)).mpr; linarith
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents, if_true,
        Bool.false_eq_true, if_false]
      rw [hv, hf]
    | gt =>
      have hh : (den : ℝ) < 2 * ((num % den : ℕ) : ℝ) := by
        exact_mod_cast (Nat.compare_eq_gt.mp hc)
      have hf : (1 : ℝ) / 2 < ((num % den : ℕ) : ℝ) / den := by
        apply (lt_div_iff₀ hdR).mpr; linarith
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents, if_true]
      rw [hv]
      constructor <;> linarith

/-- The exact accuracy construction appearing in native `sqrtCore`. Integer
square roots cannot lie exactly half way between successive integers. -/
theorem sqrt_residual_represents (n : ℕ) :
    let root := n.sqrt
    let rem := n - root * root
    Represents (ExtendedMantissa.ofMantissaAndAccuracy root
      (if rem = 0 then .exact else .inexact (if rem ≤ root then .lt else .gt)))
      (Real.sqrt (n : ℝ)) := by
  dsimp only
  have hsq : (n.sqrt : ℝ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
  have hnext : (n : ℝ) < ((n.sqrt : ℝ) + 1) * (n.sqrt + 1) := by
    exact_mod_cast Nat.lt_succ_sqrt n
  have hrem : ((n - n.sqrt * n.sqrt : ℕ) : ℝ) = (n : ℝ) - (n.sqrt : ℝ) * n.sqrt := by
    rw [Nat.cast_sub (Nat.sqrt_le n), Nat.cast_mul]
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hnonneg := Real.sqrt_nonneg (n : ℝ)
  have hroot : (0 : ℝ) ≤ n.sqrt := by positivity
  split_ifs with hz hh
  · simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents,
      Bool.false_eq_true, if_false]
    have hzR : (n : ℝ) = (n.sqrt : ℝ) * n.sqrt := by rw [hz] at hrem; norm_num at hrem; linarith
    nlinarith
  · have hpos : (0 : ℝ) < ((n - n.sqrt * n.sqrt : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    have hhR : ((n - n.sqrt * n.sqrt : ℕ) : ℝ) ≤ n.sqrt := by exact_mod_cast hh
    simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents,
      Bool.false_eq_true, if_false, if_true]
    constructor <;> nlinarith
  · have hhR : (n.sqrt : ℝ) + 1 ≤ ((n - n.sqrt * n.sqrt : ℕ) : ℝ) := by
      exact_mod_cast (show n.sqrt + 1 ≤ n - n.sqrt * n.sqrt by omega)
    simp only [ExtendedMantissa.ofMantissaAndAccuracy, Represents, if_true]
    constructor <;> nlinarith

end FP.Native
