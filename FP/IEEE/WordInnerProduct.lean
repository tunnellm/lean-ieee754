import FP.IEEE.Encoding
import FP.IEEE.InnerProduct

/-! Inner products of actual binary32/binary64 bit patterns, under the explicit
IEEE finite-value specification. This is not a bridge to native `Float` externs.
-/
noncomputable section
namespace FP.IEEE
namespace Interchange

/-- Decode finite IEEE words, multiply and add with separate nearest-even
roundings, and return the exact real value of the computed finite result.
Exceptional operands or overflow are propagated as `none`. -/
def wordDot? (I : Interchange) (x y : ℕ → I.Word) : ℕ → Option ℝ
  | 0 => some 0
  | n + 1 => do
    let s ← I.wordDot? x y n
    let a ← I.decode? (x n)
    let b ← I.decode? (y n)
    let p ← I.format.round? (a * b)
    I.format.round? (s + p)

theorem wordDot?_eq (I : Interchange) (x y : ℕ → I.Word) (n : ℕ)
    (hx : ∀ i < n, I.IsFinite (x i)) (hy : ∀ i < n, I.IsFinite (y i)) :
    I.wordDot? x y n = I.format.dot? (fun i => I.value (x i)) (fun i => I.value (y i)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    simp only [wordDot?, Format.dot?, hn,
      I.decode?_eq (x n) (hx n (by omega)), I.decode?_eq (y n) (hy n (by omega))]
    rfl

/-- Bit-pattern input version of the componentwise backward stability theorem. -/
theorem word_innerProduct_backward (I : Interchange) (x y : ℕ → I.Word) (n : ℕ)
    (hx : ∀ i < n, I.IsFinite (x i)) (hy : ∀ i < n, I.IsFinite (y i))
    (hs : I.format.SafeDot (fun i => I.value (x i)) (fun i => I.value (y i)) n)
    (hn : (2 * n : ℕ) * I.format.unitRoundoff < 1) :
    ∃ s : ℝ, I.wordDot? x y n = some s ∧
      FP.BackwardStable (FP.gamma I.format.unitRoundoff (2 * n))
        (fun i => I.value (x i)) (fun i => I.value (y i)) n s := by
  rw [I.wordDot?_eq x y n hx hy]
  exact I.format.innerProduct_backward _ _ n hs hn

end Interchange

theorem fp32_bits_innerProduct_backward (x y : ℕ → BitVec 32) (n : ℕ)
    (hx : ∀ i < n, fp32.IsFinite (x i)) (hy : ∀ i < n, fp32.IsFinite (y i))
    (hs : binary32.SafeDot (fun i => fp32.value (x i)) (fun i => fp32.value (y i)) n)
    (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-24 : ℤ) < 1) :
    ∃ s : ℝ, fp32.wordDot? x y n = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-24 : ℤ)) (2 * n))
        (fun i => fp32.value (x i)) (fun i => fp32.value (y i)) n s :=
  fp32.word_innerProduct_backward x y n hx hy hs hn

theorem fp64_bits_innerProduct_backward (x y : ℕ → BitVec 64) (n : ℕ)
    (hx : ∀ i < n, fp64.IsFinite (x i)) (hy : ∀ i < n, fp64.IsFinite (y i))
    (hs : binary64.SafeDot (fun i => fp64.value (x i)) (fun i => fp64.value (y i)) n)
    (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-53 : ℤ) < 1) :
    ∃ s : ℝ, fp64.wordDot? x y n = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-53 : ℤ)) (2 * n))
        (fun i => fp64.value (x i)) (fun i => fp64.value (y i)) n s :=
  fp64.word_innerProduct_backward x y n hx hy hs hn

end FP.IEEE
