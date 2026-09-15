import FP.Basic

/-! Mixed absolute/relative errors and denominator-free error accumulation. -/
noncomputable section
namespace FP
open scoped BigOperators

def MixedError (u ε z zhat : ℝ) : Prop := |zhat - z| ≤ u * |z| + ε

theorem mixedError_decomposition {u ε z zhat : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε) :
    MixedError u ε z zhat ↔
      ∃ δ ρ : ℝ, |δ| ≤ u ∧ |ρ| ≤ ε ∧ zhat = z * (1 + δ) + ρ := by
  constructor
  · intro h
    suffices hw : ∃ w : ℝ, |w - z| ≤ u * |z| ∧ |zhat - w| ≤ ε by
      obtain ⟨w, hw, he⟩ := hw
      obtain ⟨δ, hd, hδ⟩ := relativeError_of_abs hu hw
      exact ⟨δ, zhat - w, hd, he, by rw [← hδ]; ring⟩
    have ha : 0 ≤ u * |z| := mul_nonneg hu (abs_nonneg z)
    have hh := abs_le.mp h
    by_cases hlo : zhat - z < -(u * |z|)
    · refine ⟨z - u * |z|, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
    · by_cases hhi : u * |z| < zhat - z
      · refine ⟨z + u * |z|, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
      · exact ⟨zhat, abs_le.mpr ⟨by linarith, by linarith⟩, by simpa using hε⟩
  · rintro ⟨δ, ρ, hd, he, rfl⟩
    unfold MixedError
    calc
      |z * (1 + δ) + ρ - z| = |z * δ + ρ| := by congr 1; ring
      _ ≤ |z| * |δ| + |ρ| := by simpa [abs_mul] using abs_add_le (z * δ) ρ
      _ ≤ u * |z| + ε := by nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg z)]

theorem mixedError_zero_iff {u z zhat : ℝ} (hu : 0 ≤ u) :
    MixedError u 0 z zhat ↔ RelativeError u z zhat := by
  rw [mixedError_decomposition hu le_rfl]
  constructor
  · rintro ⟨δ, ρ, hd, he, hv⟩
    have : ρ = 0 := abs_nonpos_iff.mp he
    exact ⟨δ, hd, by simpa [this] using hv⟩
  · rintro ⟨δ, hd, hv⟩
    exact ⟨δ, 0, hd, by simp, by simpa using hv⟩

theorem MixedError.add {u ε a b a' b' c Ea Eb : ℝ} (hu : 0 ≤ u)
    (ha : |a' - a| ≤ Ea) (hb : |b' - b| ≤ Eb)
    (hc : MixedError u ε (a' + b') c) :
    |c - (a + b)| ≤ (1 + u) * (Ea + Eb) + u * |a + b| + ε := by
  have hsum : |(a' + b') - (a + b)| ≤ Ea + Eb := by
    calc
      _ = |(a' - a) + (b' - b)| := by congr 1; ring
      _ ≤ |a' - a| + |b' - b| := abs_add_le _ _
      _ ≤ Ea + Eb := add_le_add ha hb
  have hmag : |a' + b'| ≤ Ea + Eb + |a + b| := by
    have ht := abs_add_le ((a' + b') - (a + b)) (a + b)
    simp only [sub_add_cancel] at ht
    linarith
  have ht := abs_add_le (c - (a' + b')) ((a' + b') - (a + b))
  rw [sub_add_sub_cancel] at ht
  unfold MixedError at hc
  nlinarith [mul_le_mul_of_nonneg_left hmag hu]

theorem product_input_error {a b a' b' Ea Eb : ℝ}
    (ha : |a' - a| ≤ Ea) (hb : |b' - b| ≤ Eb) :
    |a' * b' - a * b| ≤ |a| * Eb + |b| * Ea + Ea * Eb := by
  have heA : 0 ≤ Ea := (abs_nonneg _).trans ha
  have heB : 0 ≤ Eb := (abs_nonneg _).trans hb
  calc
    _ = |a * (b' - b) + b * (a' - a) + (a' - a) * (b' - b)| := by congr 1; ring
    _ ≤ |a| * |b' - b| + |b| * |a' - a| + |a' - a| * |b' - b| := by
      simpa [abs_mul] using (abs_add_le (a * (b' - b) + b * (a' - a))
        ((a' - a) * (b' - b))).trans
        (add_le_add (abs_add_le (a * (b' - b)) (b * (a' - a))) le_rfl)
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
      (mul_le_mul_of_nonneg_left ha (abs_nonneg _)))
      (mul_le_mul ha hb (abs_nonneg _) heA)

theorem MixedError.mul {u ε a b a' b' c Ea Eb : ℝ} (hu : 0 ≤ u)
    (ha : |a' - a| ≤ Ea) (hb : |b' - b| ≤ Eb)
    (hc : MixedError u ε (a' * b') c) :
    |c - a * b| ≤ (1 + u) * (|a| * Eb + |b| * Ea + Ea * Eb) + u * |a * b| + ε := by
  have he := product_input_error ha hb
  have hm := abs_add_le (a' * b' - a * b) (a * b)
  simp only [sub_add_cancel] at hm
  have ht := abs_add_le (c - a' * b') (a' * b' - a * b)
  rw [sub_add_sub_cancel] at ht
  unfold MixedError at hc
  nlinarith [mul_le_mul_of_nonneg_left (hm.trans (add_le_add he le_rfl)) hu]

def geomWeight (u : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (1 + u) ^ j

@[simp] theorem geomWeight_zero (u : ℝ) : geomWeight u 0 = 0 := by simp [geomWeight]

theorem geomWeight_succ (u : ℝ) (n : ℕ) :
    geomWeight u (n + 1) = 1 + (1 + u) * geomWeight u n := by
  induction n with
  | zero => simp [geomWeight]
  | succ n ih =>
    have hs : geomWeight u (n + 1) = geomWeight u n + (1 + u) ^ n := by
      simp [geomWeight, Finset.sum_range_succ]
    have hs' : geomWeight u (n + 1 + 1) = geomWeight u (n + 1) + (1 + u) ^ (n + 1) := by
      simp [geomWeight, Finset.sum_range_succ]
    rw [hs', hs, pow_succ]
    rw [hs] at ih
    nlinarith [congrArg (fun z => (1 + u) * z) ih]

theorem geomWeight_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ geomWeight u n := by
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg (by linarith) _)

/-- A recurrence bound with no division and no smallness assumption. -/
theorem recurrence_bound {u : ℝ} (hu : 0 ≤ u) (E d : ℕ → ℝ)
    (hstep : ∀ k, E (k + 1) ≤ (1 + u) * E k + d k) (n : ℕ) :
    E n ≤ (1 + u) ^ n * E 0 + ∑ i ∈ Finset.range n, (1 + u) ^ (n - 1 - i) * d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hq : 0 ≤ 1 + u := by linarith
    calc
      E (n + 1) ≤ (1 + u) * E n + d n := hstep n
      _ ≤ (1 + u) * ((1 + u) ^ n * E 0 +
          ∑ i ∈ Finset.range n, (1 + u) ^ (n - 1 - i) * d i) + d n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
      _ = _ := by
        rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
        have hs : (∑ i ∈ Finset.range n, (1 + u) * ((1 + u) ^ (n - 1 - i) * d i)) =
            ∑ i ∈ Finset.range n, (1 + u) ^ (n + 1 - 1 - i) * d i := by
          apply Finset.sum_congr rfl
          intro i hi
          have he : n + 1 - 1 - i = (n - 1 - i) + 1 := by
            have := Finset.mem_range.mp hi
            omega
          rw [he, pow_succ]
          ring
        rw [hs, pow_succ]
        simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
        ring

@[simp] theorem geomWeight_zero_u (n : ℕ) : geomWeight 0 n = n := by
  simp [geomWeight]

end FP
