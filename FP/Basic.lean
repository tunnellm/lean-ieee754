import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Reusable relative-error and error-accumulation machinery. -/
noncomputable section
namespace FP

/-- A single operation satisfies the traditional relative-error model. -/
def RelativeError (u x y : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ y = x * (1 + δ)

theorem relativeError_of_abs {u x y : ℝ} (hu : 0 ≤ u)
    (h : |y - x| ≤ u * |x|) : RelativeError u x y := by
  by_cases hx : x = 0
  · subst x
    have hy : y = 0 := by simpa using h
    exact ⟨0, by simpa using hu, by simp [hy]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr hx)]
      exact h
    · field_simp
      ring

/-- An unconditional accumulation bound; no smallness assumption on `n*u`. -/
def growth (u : ℝ) (n : ℕ) : ℝ := (1 + u) ^ n - 1

/-- The customary rational bound, used only when `n*u < 1`. -/
def gamma (u : ℝ) (n : ℕ) : ℝ := (n * u) / (1 - n * u)

theorem growth_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ growth u n := by
  exact sub_nonneg.mpr (one_le_pow₀ (by linarith))

theorem growth_mono {u : ℝ} (hu : 0 ≤ u) {m n : ℕ} (h : m ≤ n) :
    growth u m ≤ growth u n := by
  exact sub_le_sub_right (pow_le_pow_right₀ (by linarith) h) 1

theorem factor_bound {u a b : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (ha : |a - 1| ≤ growth u m) (hb : |b - 1| ≤ growth u n) :
    |a * b - 1| ≤ growth u (m + n) := by
  have hb' : |b| ≤ (1 + u) ^ n := by
    calc
      |b| = |(b - 1) + 1| := by congr 1; ring
      _ ≤ |b - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ (1 + u) ^ n := by simpa [growth, add_comm] using add_le_add_right hb 1
  calc
    |a * b - 1| = |(a - 1) * b + (b - 1)| := by congr 1; ring
    _ ≤ |a - 1| * |b| + |b - 1| := by
      simpa [abs_mul] using abs_add_le ((a - 1) * b) (b - 1)
    _ ≤ growth u m * (1 + u) ^ n + growth u n :=
      add_le_add (mul_le_mul ha hb' (abs_nonneg _) (growth_nonneg hu _)) hb
    _ = growth u (m + n) := by simp [growth, pow_add]; ring

theorem one_add_error {u δ : ℝ} (h : |δ| ≤ u) :
    |(1 + δ) - 1| ≤ growth u 1 := by simpa [growth] using h

/-- Converts the exponential accumulation bound to the conventional gamma bound. -/
theorem growth_le_gamma {u : ℝ} (hu : 0 ≤ u) (n : ℕ) (hn : n * u < 1) :
    growth u n ≤ gamma u n := by
  have haux : ∀ k : ℕ, k ≤ n → (1 + u) ^ k * (1 - k * u) ≤ 1 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ n := by omega
      have hp : 0 ≤ (1 + u) ^ k := pow_nonneg (by linarith) _
      have hh := ih hk'
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg hp (mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        (sq_nonneg u)), mul_nonneg hp (sq_nonneg u)]
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  rw [growth, gamma, le_div_iff₀ hden]
  nlinarith [haux n le_rfl]

end FP
