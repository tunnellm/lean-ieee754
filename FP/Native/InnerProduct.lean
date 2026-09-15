import FP.Native.Bridge
import FP.IEEE.InnerProduct

/-! Sequential native inner products, their specification equivalence, and
componentwise backward stability. Multiplication and addition round separately. -/
namespace FP.Native

/-- Executable left-to-right inner product over the supplied operations. -/
def nativeDot {α : Type} (zero : α) (add mul : α → α → α)
    (x y : ℕ → α) : ℕ → α
  | 0 => zero
  | n + 1 => add (nativeDot zero add mul x y n) (mul (x n) (y n))

def floatDot (x y : ℕ → Float) : ℕ → Float :=
  nativeDot (Float.ofBits 0) (· + ·) (· * ·) x y

def float32Dot (x y : ℕ → Float32) : ℕ → Float32 :=
  nativeDot (Float32.ofBits 0) (· + ·) (· * ·) x y

noncomputable section

/-- This equivalence requires only nonoverflow, allowing gradual underflow. -/
theorem nativeDot_value {α : Type} (F : FP.IEEE.Format)
    (zero : α) (add mul : α → α → α) (value : α → Option ℝ)
    (hz : value zero = some 0)
    (ha : ∀ a b x y, value a = some x → value b = some y →
      |x + y| < F.overflowThreshold → value (add a b) = F.round? (x + y))
    (hm : ∀ a b x y, value a = some x → value b = some y →
      |x * y| < F.overflowThreshold → value (mul a b) = F.round? (x * y))
    (a b : ℕ → α) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, value (a i) = some (x i))
    (hy : ∀ i < n, value (b i) = some (y i))
    (hs : FP.SafeTrace (fun t => |t| < F.overflowThreshold) F.roundFinite x y n) :
    value (nativeDot zero add mul a b n) = some (FP.roundedDot F.roundFinite x y n) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have hn := ih (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
      (fun i hi => hs i (by omega))
    have hp := hm (a n) (b n) (x n) (y n) (hx n (by omega)) (hy n (by omega))
      (hs n (by omega)).1
    rw [FP.IEEE.Format.round?, if_pos (hs n (by omega)).1] at hp
    rw [nativeDot, ha _ _ _ _ hn hp (hs n (by omega)).2]
    rw [FP.IEEE.Format.round?, if_pos (hs n (by omega)).2]
    rfl

theorem safe_nonoverflow (F : FP.IEEE.Format) {x : ℝ} (hx : F.Safe x) :
    |x| < F.overflowThreshold := by
  rcases hx with rfl | hx
  · simpa using F.overflowThreshold_pos
  · exact hx.2

theorem floatDot_value (a b : ℕ → Float) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hs : FP.SafeTrace (fun t => |t| < FP.IEEE.binary64.overflowThreshold)
      FP.IEEE.binary64.roundFinite x y n) :
    floatValue (floatDot a b n) = some (FP.roundedDot FP.IEEE.binary64.roundFinite x y n) :=
  nativeDot_value _ _ _ _ _ floatValue_zero float_add_equiv float_mul_equiv a b x y n hx hy hs

theorem float32Dot_value (a b : ℕ → Float32) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hs : FP.SafeTrace (fun t => |t| < FP.IEEE.binary32.overflowThreshold)
      FP.IEEE.binary32.roundFinite x y n) :
    float32Value (float32Dot a b n) = some (FP.roundedDot FP.IEEE.binary32.roundFinite x y n) :=
  nativeDot_value _ _ _ _ _ float32Value_zero float32_add_equiv float32_mul_equiv a b x y n hx hy hs

theorem float_innerProduct_backward (a b : ℕ → Float) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hs : FP.IEEE.binary64.SafeDot x y n)
    (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-53 : ℤ) < 1) :
    ∃ s : ℝ, floatValue (floatDot a b n) = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-53 : ℤ)) (2 * n)) x y n s := by
  obtain ⟨s, he, hb⟩ := FP.IEEE.binary64_innerProduct_backward x y n hs hn
  rw [FP.IEEE.Format.dot?_eq_of_safe _ _ _ _ hs] at he
  have hev := floatDot_value a b x y n hx hy (fun i hi =>
    ⟨safe_nonoverflow _ (hs i hi).1, safe_nonoverflow _ (hs i hi).2⟩)
  exact ⟨s, hev.trans he, hb⟩

theorem float32_innerProduct_backward (a b : ℕ → Float32) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hs : FP.IEEE.binary32.SafeDot x y n)
    (hn : (2 * n : ℕ) * (2 : ℝ) ^ (-24 : ℤ) < 1) :
    ∃ s : ℝ, float32Value (float32Dot a b n) = some s ∧
      FP.BackwardStable (FP.gamma ((2 : ℝ) ^ (-24 : ℤ)) (2 * n)) x y n s := by
  obtain ⟨s, he, hb⟩ := FP.IEEE.binary32_innerProduct_backward x y n hs hn
  rw [FP.IEEE.Format.dot?_eq_of_safe _ _ _ _ hs] at he
  have hev := float32Dot_value a b x y n hx hy (fun i hi =>
    ⟨safe_nonoverflow _ (hs i hi).1, safe_nonoverflow _ (hs i hi).2⟩)
  exact ⟨s, hev.trans he, hb⟩

theorem dot?_eq_of_nonoverflow (F : FP.IEEE.Format) (x y : ℕ → ℝ) (n : ℕ)
    (hs : FP.SafeTrace (fun t => |t| < F.overflowThreshold) F.roundFinite x y n) :
    F.dot? x y n = some (FP.roundedDot F.roundFinite x y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun i hi => hs i (by omega))
    simp only [FP.IEEE.Format.dot?, hn, FP.IEEE.Format.round?,
      if_pos (hs n (by omega)).1]
    change F.round? (FP.roundedDot F.roundFinite x y n + F.roundFinite (x n * y n)) = _
    rw [FP.IEEE.Format.round?, if_pos (hs n (by omega)).2]
    rfl

theorem floatDot_equiv (a b : ℕ → Float) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hs : FP.SafeTrace (fun t => |t| < FP.IEEE.binary64.overflowThreshold)
      FP.IEEE.binary64.roundFinite x y n) :
    floatValue (floatDot a b n) = FP.IEEE.binary64.dot? x y n :=
  (floatDot_value a b x y n hx hy hs).trans (dot?_eq_of_nonoverflow _ x y n hs).symm

theorem float32Dot_equiv (a b : ℕ → Float32) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hs : FP.SafeTrace (fun t => |t| < FP.IEEE.binary32.overflowThreshold)
      FP.IEEE.binary32.roundFinite x y n) :
    float32Value (float32Dot a b n) = FP.IEEE.binary32.dot? x y n :=
  (float32Dot_value a b x y n hx hy hs).trans (dot?_eq_of_nonoverflow _ x y n hs).symm

end
end FP.Native
