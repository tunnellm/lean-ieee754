import FP.MixedError
import FP.MixedBackward
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Log

/-! Addition schedules shared by specifications, native evaluators, and certificates. -/
namespace FP

inductive ReductionTree where
  | zero
  | input (i : ℕ)
  | add (left right : ReductionTree)
  deriving Repr, DecidableEq

namespace ReductionTree

def eval {α : Type} (zero : α) (add : α → α → α) (x : ℕ → α) : ReductionTree → α
  | .zero => zero
  | .input i => x i
  | .add l r => add (eval zero add x l) (eval zero add x r)

def leaves : ReductionTree → List ℕ
  | .zero => []
  | .input i => [i]
  | .add l r => l.leaves ++ r.leaves

def height : ReductionTree → ℕ
  | .zero | .input _ => 0
  | .add l r => max l.height r.height + 1

def additions : ReductionTree → ℕ
  | .zero | .input _ => 0
  | .add l r => l.additions + r.additions + 1

noncomputable def roundWeight (u : ℝ) : ReductionTree → ℝ
  | .zero | .input _ => 0
  | .add l r => 1 + (1 + u) * (l.roundWeight u + r.roundWeight u)

noncomputable def rounded (r : ℝ → ℝ) (x : ℕ → ℝ) : ReductionTree → ℝ :=
  eval 0 (fun a b => r (a + b)) x

noncomputable def exactSum (x : ℕ → ℝ) : ReductionTree → ℝ := eval 0 (· + ·) x
noncomputable def mass (x : ℕ → ℝ) : ReductionTree → ℝ := exactSum (fun i => |x i|)

/-- Obligations concern the exact input of each rounding operation. -/
def Trace (P : ℝ → Prop) (r : ℝ → ℝ) (x : ℕ → ℝ) : ReductionTree → Prop
  | .zero | .input _ => True
  | .add l t => l.Trace P r x ∧ t.Trace P r x ∧ P (l.rounded r x + t.rounded r x)

theorem exactSum_leaves (t : ReductionTree) (x : ℕ → ℝ) :
    t.exactSum x = (t.leaves.map x).sum := by
  induction t with
  | zero => rfl
  | input i => simp [exactSum, eval, leaves]
  | add l r hl hr => simpa [exactSum, eval, leaves] using congrArg₂ (· + ·) hl hr

theorem mass_nonneg (t : ReductionTree) (x : ℕ → ℝ) : 0 ≤ t.mass x := by
  induction t with
  | zero => exact le_rfl
  | input i => exact abs_nonneg _
  | add l r hl hr => exact add_nonneg hl hr

theorem abs_exactSum_le_mass (t : ReductionTree) (x : ℕ → ℝ) :
    |t.exactSum x| ≤ t.mass x := by
  induction t with
  | zero => simp [exactSum, eval, mass]
  | input i => exact le_rfl
  | add l r hl hr => exact (abs_add_le _ _).trans (add_le_add hl hr)

theorem roundWeight_nonneg {u : ℝ} (hu : 0 ≤ u) (t : ReductionTree) :
    0 ≤ t.roundWeight u := by
  induction t with
  | zero => exact le_rfl
  | input i => exact le_rfl
  | add l r hl hr => simp only [roundWeight]; positivity

/-- Tree depth controls relative error; internal-node depths control absolute error. -/
theorem mixed_error {u ε : ℝ} (hu : 0 ≤ u) (_hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (t : ReductionTree) (x : ℕ → ℝ) (hs : t.Trace P r x) :
    |t.rounded r x - t.exactSum x| ≤ growth u t.height * t.mass x + ε * t.roundWeight u := by
  induction t with
  | zero => simp [rounded, exactSum, eval, height, mass, roundWeight, growth]
  | input i => simp [rounded, exactSum, eval, height, mass, roundWeight, growth]
  | add l t hl ht =>
    have hstep := MixedError.add hu (hl hs.1) (ht hs.2.1) (hr _ hs.2.2)
    have hlm := l.mass_nonneg x
    have htm := t.mass_nonneg x
    have hgl := growth_mono hu (Nat.le_max_left l.height t.height)
    have hgt := growth_mono hu (Nat.le_max_right l.height t.height)
    have hm := (abs_add_le (l.exactSum x) (t.exactSum x)).trans
      (add_le_add (l.abs_exactSum_le_mass x) (t.abs_exactSum_le_mass x))
    change |r (l.rounded r x + t.rounded r x) - (l.exactSum x + t.exactSum x)| ≤ _
    simp only [height, mass, exactSum, eval, roundWeight]
    change |r (l.rounded r x + t.rounded r x) - (l.exactSum x + t.exactSum x)| ≤ growth u (max l.height t.height + 1) * (l.mass x + t.mass x) +
      ε * (1 + (1 + u) * (l.roundWeight u + t.roundWeight u))
    have hleft := mul_le_mul_of_nonneg_right hgl hlm
    have hright := mul_le_mul_of_nonneg_right hgt htm
    have hg : growth u (max l.height t.height + 1) =
        (1 + u) * growth u (max l.height t.height) + u := by
      simp [growth, pow_succ]; ring
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hleft hright) (by linarith : 0 ≤ 1 + u),
      mul_le_mul_of_nonneg_left hm hu]

theorem roundWeight_le {u : ℝ} (hu : 0 ≤ u) (t : ReductionTree) :
    t.roundWeight u ≤ (t.additions : ℝ) * (1 + u) ^ (t.height - 1) := by
  induction t with
  | zero => simp [roundWeight, additions]
  | input i => simp [roundWeight, additions]
  | add l r hl hr =>
    let h := max l.height r.height
    have hh : (1 : ℝ) ≤ (1 + u) ^ h := one_le_pow₀ (by linarith)
    have child : ∀ c : ReductionTree, c.height ≤ h →
        c.roundWeight u ≤ c.additions * (1 + u) ^ (c.height - 1) →
        (1 + u) * c.roundWeight u ≤ c.additions * (1 + u) ^ h := by
      intro c hc he
      by_cases hz : c.height = 0
      · cases c <;> simp_all [height, additions, roundWeight]
      · have hp := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + u)
          (show c.height - 1 + 1 ≤ h by omega)
        have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 1 + u)
        have hm' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg c.additions : (0 : ℝ) ≤ c.additions)
        rw [pow_succ] at hm'
        nlinarith
    have hcl := child l (Nat.le_max_left _ _) hl
    have hcr := child r (Nat.le_max_right _ _) hr
    simp only [roundWeight, height, additions, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    change _ ≤ ((l.additions : ℝ) + r.additions + 1) * (1 + u) ^ h
    nlinarith

end ReductionTree

/-- No initial addition to zero: a singleton is returned unchanged. -/
def sequentialTree (start : ℕ) : ℕ → ReductionTree
  | 0 => .zero
  | 1 => .input start
  | n + 2 => .add (sequentialTree start (n + 1)) (.input (start + n + 1))

/-- Contiguous balanced splitting without padding, including arbitrary odd lengths. -/
def pairwiseTree (start n : ℕ) : ReductionTree :=
  if h0 : n = 0 then .zero
  else if h1 : n = 1 then .input start
  else .add (pairwiseTree start (n / 2)) (pairwiseTree (start + n / 2) (n - n / 2))
termination_by n

theorem sequentialTree_leaves (start n : ℕ) :
    (sequentialTree start n).leaves = List.range' start n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [sequentialTree, ReductionTree.leaves]
  | more n _ ih =>
    simp only [sequentialTree, ReductionTree.leaves, ih]
    have h := @List.range'_append start (n + 1) 1 1
    simpa [List.range'_succ, Nat.add_assoc] using h

theorem pairwiseTree_leaves (start n : ℕ) :
    (pairwiseTree start n).leaves = List.range' start n := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    rw [pairwiseTree]
    split_ifs with h0 h1
    · simp [h0, ReductionTree.leaves]
    · simp [h1, ReductionTree.leaves]
    · simp only [ReductionTree.leaves, ih (n / 2) (by omega), ih (n - n / 2) (by omega)]
      simpa only [one_mul, Nat.add_sub_of_le (Nat.div_le_self n 2)] using
        (@List.range'_append start (n / 2) (n - n / 2) 1)

theorem sequentialTree_height (start n : ℕ) : (sequentialTree start n).height = n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih => simp [sequentialTree, ReductionTree.height, ih]

theorem sequentialTree_additions (start n : ℕ) : (sequentialTree start n).additions = n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih => simp [sequentialTree, ReductionTree.additions, ih]

theorem pairwiseTree_height (start n : ℕ) : (pairwiseTree start n).height = Nat.clog 2 n := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    rw [pairwiseTree]
    split_ifs with h0 h1
    · simp [h0, ReductionTree.height]
    · simp [h1, ReductionTree.height]
    · simp only [ReductionTree.height, ih (n / 2) (by omega), ih (n - n / 2) (by omega)]
      have he : n - n / 2 = (n + 2 - 1) / 2 := by omega
      have hm := Nat.clog_mono_right 2 (show n / 2 ≤ n - n / 2 by omega)
      rw [max_eq_right hm, he, Nat.clog_of_two_le (by decide : 1 < 2) (by omega : 2 ≤ n)]

theorem pairwiseTree_additions (start n : ℕ) : (pairwiseTree start n).additions = n - 1 := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    rw [pairwiseTree]
    split_ifs with h0 h1
    · simp [h0, ReductionTree.additions]
    · simp [h1, ReductionTree.additions]
    · simp only [ReductionTree.additions, ih (n / 2) (by omega), ih (n - n / 2) (by omega)]
      omega

theorem sequentialTree_roundWeight (u : ℝ) (start n : ℕ) :
    (sequentialTree start n).roundWeight u = geomWeight u (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sequentialTree, ReductionTree.roundWeight]
  | one => simp [sequentialTree, ReductionTree.roundWeight]
  | more n _ ih => simp [sequentialTree, ReductionTree.roundWeight, ih, geomWeight_succ]

noncomputable def sequentialSum (r : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (sequentialTree 0 n).rounded r x
noncomputable def pairwiseSum (r : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (pairwiseTree 0 n).rounded r x

open scoped BigOperators

theorem sequentialTree_exactSum (x : ℕ → ℝ) (n : ℕ) :
    (sequentialTree 0 n).exactSum x = ∑ i ∈ Finset.range n, x i := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sequentialTree, ReductionTree.exactSum, ReductionTree.eval]
  | one => simp [sequentialTree, ReductionTree.exactSum, ReductionTree.eval]
  | more n _ ih =>
    simp only [sequentialTree, ReductionTree.exactSum, ReductionTree.eval, zero_add]
    change (sequentialTree 0 (n + 1)).exactSum x + x (n + 1) = _
    rw [ih]
    simp only [Finset.sum_range_succ]

theorem pairwiseTree_exactSum (x : ℕ → ℝ) (n : ℕ) :
    (pairwiseTree 0 n).exactSum x = ∑ i ∈ Finset.range n, x i := by
  rw [ReductionTree.exactSum_leaves, pairwiseTree_leaves,
    ← sequentialTree_leaves, ← ReductionTree.exactSum_leaves, sequentialTree_exactSum]

theorem sequentialSum_mixed_error {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (sequentialTree 0 n).Trace P r x) :
    |sequentialSum r x n - ∑ i ∈ Finset.range n, x i| ≤
      growth u (n - 1) * (∑ i ∈ Finset.range n, |x i|) + ε * geomWeight u (n - 1) := by
  simpa only [sequentialSum, sequentialTree_exactSum, ReductionTree.mass,
    sequentialTree_height, sequentialTree_roundWeight] using
    (sequentialTree 0 n).mixed_error hu hε r P hr x hs

theorem pairwiseSum_mixed_error {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (pairwiseTree 0 n).Trace P r x) :
    |pairwiseSum r x n - ∑ i ∈ Finset.range n, x i| ≤
      growth u (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
        ε * (pairwiseTree 0 n).roundWeight u := by
  simpa only [pairwiseSum, pairwiseTree_exactSum, ReductionTree.mass,
    pairwiseTree_height] using (pairwiseTree 0 n).mixed_error hu hε r P hr x hs

theorem pairwiseSum_mixed_error_coarse {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (pairwiseTree 0 n).Trace P r x) :
    |pairwiseSum r x n - ∑ i ∈ Finset.range n, x i| ≤
      growth u (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
        ε * ((n - 1 : ℕ) : ℝ) * (1 + u) ^ (Nat.clog 2 n - 1) := by
  have hw := (pairwiseTree 0 n).roundWeight_le hu
  rw [pairwiseTree_additions, pairwiseTree_height] at hw
  exact (pairwiseSum_mixed_error hu hε r P hr x n hs).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hw hε])

theorem sum_backward_of_abs {β : ℝ} (hβ : 0 ≤ β) (x : ℕ → ℝ) (n : ℕ) (s : ℝ)
    (hs : |s - ∑ i ∈ Finset.range n, x i| ≤ β * ∑ i ∈ Finset.range n, |x i|) :
    BackwardStable β x (fun _ => 1) n s := by
  apply (mixedBackwardStable_zero_iff β x (fun _ => 1) n s).mp
  apply mixedBackwardStable_of_abs hβ le_rfl
  simpa [dotMass] using hs

theorem sequentialSum_mixed_error_gamma {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (sequentialTree 0 n).Trace P r x)
    (hn : ((n - 1 : ℕ) : ℝ) * u < 1) :
    |sequentialSum r x n - ∑ i ∈ Finset.range n, x i| ≤
      gamma u (n - 1) * (∑ i ∈ Finset.range n, |x i|) + ε * geomWeight u (n - 1) :=
  (sequentialSum_mixed_error hu hε r P hr x n hs).trans
    (add_le_add (mul_le_mul_of_nonneg_right (growth_le_gamma hu _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)

theorem pairwiseSum_mixed_error_gamma {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → MixedError u ε z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (pairwiseTree 0 n).Trace P r x)
    (hn : (Nat.clog 2 n : ℝ) * u < 1) :
    |pairwiseSum r x n - ∑ i ∈ Finset.range n, x i| ≤
      gamma u (Nat.clog 2 n) * (∑ i ∈ Finset.range n, |x i|) +
        ε * (pairwiseTree 0 n).roundWeight u :=
  (pairwiseSum_mixed_error hu hε r P hr x n hs).trans
    (add_le_add (mul_le_mul_of_nonneg_right (growth_le_gamma hu _ hn)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) le_rfl)

theorem sequentialSum_backward {u : ℝ} (hu : 0 ≤ u)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (sequentialTree 0 n).Trace P r x) :
    BackwardStable (growth u (n - 1)) x (fun _ => 1) n (sequentialSum r x n) := by
  apply sum_backward_of_abs (growth_nonneg hu _)
  simpa using sequentialSum_mixed_error hu (le_refl (0 : ℝ)) r P
    (fun z hz => (mixedError_zero_iff hu).mpr (hr z hz)) x n hs

theorem pairwiseSum_backward {u : ℝ} (hu : 0 ≤ u)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (pairwiseTree 0 n).Trace P r x) :
    BackwardStable (growth u (Nat.clog 2 n)) x (fun _ => 1) n (pairwiseSum r x n) := by
  apply sum_backward_of_abs (growth_nonneg hu _)
  simpa using pairwiseSum_mixed_error hu (le_refl (0 : ℝ)) r P
    (fun z hz => (mixedError_zero_iff hu).mpr (hr z hz)) x n hs

@[simp] theorem mem_sequentialTree_leaves (i n : ℕ) :
    i ∈ (sequentialTree 0 n).leaves ↔ i < n := by
  rw [sequentialTree_leaves, List.range'_eq_map_range]
  simp

@[simp] theorem mem_pairwiseTree_leaves (i n : ℕ) :
    i ∈ (pairwiseTree 0 n).leaves ↔ i < n := by
  rw [pairwiseTree_leaves, List.range'_eq_map_range]
  simp

theorem sequentialSum_backward_gamma {u : ℝ} (hu : 0 ≤ u)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (sequentialTree 0 n).Trace P r x)
    (hn : ((n - 1 : ℕ) : ℝ) * u < 1) :
    BackwardStable (gamma u (n - 1)) x (fun _ => 1) n (sequentialSum r x n) :=
  (sequentialSum_backward hu r P hr x n hs).mono (growth_le_gamma hu _ hn)

theorem pairwiseSum_backward_gamma {u : ℝ} (hu : 0 ≤ u)
    (r : ℝ → ℝ) (P : ℝ → Prop) (hr : ∀ z, P z → RelativeError u z (r z))
    (x : ℕ → ℝ) (n : ℕ) (hs : (pairwiseTree 0 n).Trace P r x)
    (hn : (Nat.clog 2 n : ℝ) * u < 1) :
    BackwardStable (gamma u (Nat.clog 2 n)) x (fun _ => 1) n (pairwiseSum r x n) :=
  (pairwiseSum_backward hu r P hr x n hs).mono (growth_le_gamma hu _ hn)

end FP
