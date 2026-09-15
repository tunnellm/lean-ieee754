import FP.Range.Interval
import FP.Summation
import FP.InnerProduct

/-! Executable certificates for addition trees and sequential dot products. -/
namespace FP.Range

/-- Leaf intervals must be well formed. Every addition is checked before rounding. -/
def checkSum (p : Params) (bounds : ℕ → Interval) : ReductionTree → Option Interval
  | .zero => some .zero
  | .input i => if (bounds i).Valid then some (bounds i) else none
  | .add l r => do
    let L ← checkSum p bounds l
    let R ← checkSum p bounds r
    checkRound p (L.add R)

/-- This checker follows the existing dot algorithm, including its first addition to zero. -/
def checkDot (p : Params) (bx bys : ℕ → Interval) : ℕ → Option Interval
  | 0 => some .zero
  | n + 1 => do
    let S ← checkDot p bx bys n
    if (bx n).Valid ∧ (bys n).Valid then do
      let P ← checkRound p ((bx n).mul (bys n))
      checkRound p (S.add P)
    else none

theorem checkSum_sound (F : FP.IEEE.Format) (bounds : ℕ → Interval) (x : ℕ → ℝ)
    (t : ReductionTree) (hx : ∀ i ∈ t.leaves, (bounds i).Contains (x i))
    {I : Interval} (hc : checkSum (.ofFormat F) bounds t = some I) :
    t.Trace (fun z => |z| < F.overflowThreshold) F.roundFinite x ∧
      I.Contains (t.rounded F.roundFinite x) := by
  induction t generalizing I with
  | zero =>
    have : Interval.zero = I := Option.some.inj hc
    subst I
    exact ⟨trivial, Interval.contains_zero⟩
  | input i =>
    simp only [checkSum] at hc
    split_ifs at hc with hv
    · have : bounds i = I := Option.some.inj hc
      subst I
      exact ⟨trivial, hx i (by simp [ReductionTree.leaves])⟩
  | add l r hl hr =>
    simp only [checkSum] at hc
    cases hL : checkSum (.ofFormat F) bounds l with
    | none => simp [hL] at hc
    | some L =>
      cases hR : checkSum (.ofFormat F) bounds r with
      | none => simp [hL, hR] at hc
      | some R =>
        have hC : checkRound (.ofFormat F) (L.add R) = some I := by simpa [hL, hR] using hc
        obtain ⟨hlT, hlV⟩ := hl (fun i hi => hx i (by simp [ReductionTree.leaves, hi])) hL
        obtain ⟨hrT, hrV⟩ := hr (fun i hi => hx i (by simp [ReductionTree.leaves, hi])) hR
        obtain ⟨hs, hv⟩ := checkRound_sound F (Interval.contains_add hlV hrV) hC
        exact ⟨⟨hlT, hrT, hs⟩, hv⟩

theorem checkDot_sound (F : FP.IEEE.Format) (bx bys : ℕ → Interval) (x y : ℕ → ℝ)
    (n : ℕ) (hx : ∀ i < n, (bx i).Contains (x i))
    (hy : ∀ i < n, (bys i).Contains (y i))
    {I : Interval} (hc : checkDot (.ofFormat F) bx bys n = some I) :
    SafeTrace (fun z => |z| < F.overflowThreshold) F.roundFinite x y n ∧
      I.Contains (roundedDot F.roundFinite x y n) := by
  induction n generalizing I with
  | zero =>
    have : Interval.zero = I := Option.some.inj hc
    subst I
    exact ⟨fun i hi => by omega, Interval.contains_zero⟩
  | succ n ih =>
    simp only [checkDot] at hc
    cases hS : checkDot (.ofFormat F) bx bys n with
    | none => simp [hS] at hc
    | some S =>
      have hvalid : (bx n).Valid ∧ (bys n).Valid :=
        ⟨Interval.valid_of_contains (hx n (by omega)), Interval.valid_of_contains (hy n (by omega))⟩
      cases hP : checkRound (.ofFormat F) ((bx n).mul (bys n)) with
      | none => simp [hS, hvalid, hP] at hc
      | some P =>
        have hC : checkRound (.ofFormat F) (S.add P) = some I := by
          simpa [hS, hvalid, hP] using hc
        obtain ⟨htrace, hvalue⟩ := ih (fun i hi => hx i (by omega))
          (fun i hi => hy i (by omega)) hS
        obtain ⟨hp, hvp⟩ := checkRound_sound F
          (Interval.contains_mul (hx n (by omega)) (hy n (by omega))) hP
        obtain ⟨ha, hva⟩ := checkRound_sound F (Interval.contains_add hvalue hvp) hC
        refine ⟨?_, hva⟩
        intro i hi
        by_cases he : i = n
        · subst i; exact ⟨hp, ha⟩
        · exact htrace i (by omega)

end FP.Range
