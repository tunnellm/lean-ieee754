import FP.Native.InnerProduct
import FP.MixedBackward
import FP.IEEE.MixedDot
import FP.Range.Checker

noncomputable section
namespace FP.Native
open scoped BigOperators

/-- Generic native transfer: the absolute residual permits gradual underflow. -/
theorem nativeDot_mixed_backward {α : Type} (F : FP.IEEE.Format)
    (zero : α) (add mul : α → α → α) (value : α → Option ℝ)
    (hz : value zero = some 0)
    (ha : ∀ a b x y, value a = some x → value b = some y →
      |x + y| < F.overflowThreshold → value (add a b) = F.round? (x + y))
    (hm : ∀ a b x y, value a = some x → value b = some y →
      |x * y| < F.overflowThreshold → value (mul a b) = F.round? (x * y))
    (a b : ℕ → α) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, value (a i) = some (x i))
    (hy : ∀ i < n, value (b i) = some (y i))
    (hs : SafeTrace (fun z => |z| < F.overflowThreshold) F.roundFinite x y n) :
    ∃ s : ℝ, value (nativeDot zero add mul a b n) = some s ∧
      MixedBackwardStable (growth F.unitRoundoff (2 * n))
        (dotResidual F.unitRoundoff (F.minSubnormal / 2) n) x y n s := by
  refine ⟨roundedDot F.roundFinite x y n, nativeDot_value F zero add mul value hz ha hm a b x y n hx hy hs, ?_⟩
  exact roundedDot_mixed_backward F.unitRoundoff_pos.le
    (by unfold FP.IEEE.Format.minSubnormal; positivity) F.roundFinite _
    (fun z _ => F.roundFinite_mixed_error z) x y n hs

theorem nativeDot_mixed_of_certificate {α : Type} (F : FP.IEEE.Format)
    (zero : α) (add mul : α → α → α) (value : α → Option ℝ)
    (hz : value zero = some 0)
    (ha : ∀ a b x y, value a = some x → value b = some y →
      |x + y| < F.overflowThreshold → value (add a b) = F.round? (x + y))
    (hm : ∀ a b x y, value a = some x → value b = some y →
      |x * y| < F.overflowThreshold → value (mul a b) = F.round? (x * y))
    (a b : ℕ → α) (x y : ℕ → ℝ) (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, value (a i) = some (x i))
    (hy : ∀ i < n, value (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat F) bx bys n).isSome = true) :
    ∃ s : ℝ, value (nativeDot zero add mul a b n) = some s ∧
      MixedBackwardStable (growth F.unitRoundoff (2 * n))
        (dotResidual F.unitRoundoff (F.minSubnormal / 2) n) x y n s := by
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.mp hc
  exact nativeDot_mixed_backward F zero add mul value hz ha hm a b x y n hx hy
    (FP.Range.checkDot_sound F bx bys x y n hbx hby hI).1

theorem floatDot_mixed_backward (a b : ℕ → Float) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hs : SafeTrace (fun z => |z| < FP.IEEE.binary64.overflowThreshold) FP.IEEE.binary64.roundFinite x y n) :
    ∃ s : ℝ, floatValue (floatDot a b n) = some s ∧
      MixedBackwardStable (growth FP.IEEE.binary64.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary64.unitRoundoff (FP.IEEE.binary64.minSubnormal / 2) n) x y n s :=
  nativeDot_mixed_backward _ _ _ _ _ floatValue_zero float_add_equiv float_mul_equiv
    a b x y n hx hy hs

theorem floatDot_mixed_of_certificate (a b : ℕ → Float) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary64) bx bys n).isSome = true) :
    ∃ s : ℝ, floatValue (floatDot a b n) = some s ∧
      MixedBackwardStable (growth FP.IEEE.binary64.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary64.unitRoundoff (FP.IEEE.binary64.minSubnormal / 2) n) x y n s :=
  nativeDot_mixed_of_certificate _ _ _ _ _ floatValue_zero float_add_equiv float_mul_equiv
    a b x y bx bys n hx hy hbx hby hc

theorem floatDot_mixed_gamma_of_certificate (a b : ℕ → Float) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary64) bx bys n).isSome = true)
    (hn : (2 * n : ℕ) * FP.IEEE.binary64.unitRoundoff < 1) :
    ∃ s : ℝ, floatValue (floatDot a b n) = some s ∧
      MixedBackwardStable (gamma FP.IEEE.binary64.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary64.unitRoundoff (FP.IEEE.binary64.minSubnormal / 2) n) x y n s := by
  obtain ⟨s, hv, he⟩ := floatDot_mixed_of_certificate a b x y bx bys n hx hy hbx hby hc
  exact ⟨s, hv, he.mono (growth_le_gamma FP.IEEE.binary64.unitRoundoff_pos.le _ hn) le_rfl⟩

theorem floatDot_mixed_forward_of_certificate (a b : ℕ → Float) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, floatValue (a i) = some (x i))
    (hy : ∀ i < n, floatValue (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary64) bx bys n).isSome = true) :
    ∃ s : ℝ, floatValue (floatDot a b n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i * y i| ≤
        growth FP.IEEE.binary64.unitRoundoff (2 * n) * dotMass x y n +
          dotResidual FP.IEEE.binary64.unitRoundoff (FP.IEEE.binary64.minSubnormal / 2) n := by
  obtain ⟨s, hv, he⟩ := floatDot_mixed_of_certificate a b x y bx bys n hx hy hbx hby hc
  exact ⟨s, hv, he.forward⟩

theorem float32Dot_mixed_backward (a b : ℕ → Float32) (x y : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hs : SafeTrace (fun z => |z| < FP.IEEE.binary32.overflowThreshold) FP.IEEE.binary32.roundFinite x y n) :
    ∃ s : ℝ, float32Value (float32Dot a b n) = some s ∧
      MixedBackwardStable (growth FP.IEEE.binary32.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary32.unitRoundoff (FP.IEEE.binary32.minSubnormal / 2) n) x y n s :=
  nativeDot_mixed_backward _ _ _ _ _ float32Value_zero float32_add_equiv float32_mul_equiv
    a b x y n hx hy hs

theorem float32Dot_mixed_of_certificate (a b : ℕ → Float32) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary32) bx bys n).isSome = true) :
    ∃ s : ℝ, float32Value (float32Dot a b n) = some s ∧
      MixedBackwardStable (growth FP.IEEE.binary32.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary32.unitRoundoff (FP.IEEE.binary32.minSubnormal / 2) n) x y n s :=
  nativeDot_mixed_of_certificate _ _ _ _ _ float32Value_zero float32_add_equiv float32_mul_equiv
    a b x y bx bys n hx hy hbx hby hc

theorem float32Dot_mixed_gamma_of_certificate (a b : ℕ → Float32) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary32) bx bys n).isSome = true)
    (hn : (2 * n : ℕ) * FP.IEEE.binary32.unitRoundoff < 1) :
    ∃ s : ℝ, float32Value (float32Dot a b n) = some s ∧
      MixedBackwardStable (gamma FP.IEEE.binary32.unitRoundoff (2 * n))
        (dotResidual FP.IEEE.binary32.unitRoundoff (FP.IEEE.binary32.minSubnormal / 2) n) x y n s := by
  obtain ⟨s, hv, he⟩ := float32Dot_mixed_of_certificate a b x y bx bys n hx hy hbx hby hc
  exact ⟨s, hv, he.mono (growth_le_gamma FP.IEEE.binary32.unitRoundoff_pos.le _ hn) le_rfl⟩

theorem float32Dot_mixed_forward_of_certificate (a b : ℕ → Float32) (x y : ℕ → ℝ)
    (bx bys : ℕ → FP.Range.Interval) (n : ℕ)
    (hx : ∀ i < n, float32Value (a i) = some (x i))
    (hy : ∀ i < n, float32Value (b i) = some (y i))
    (hbx : ∀ i < n, (bx i).Contains (x i))
    (hby : ∀ i < n, (bys i).Contains (y i))
    (hc : (FP.Range.checkDot (.ofFormat FP.IEEE.binary32) bx bys n).isSome = true) :
    ∃ s : ℝ, float32Value (float32Dot a b n) = some s ∧
      |s - ∑ i ∈ Finset.range n, x i * y i| ≤
        growth FP.IEEE.binary32.unitRoundoff (2 * n) * dotMass x y n +
          dotResidual FP.IEEE.binary32.unitRoundoff (FP.IEEE.binary32.minSubnormal / 2) n := by
  obtain ⟨s, hv, he⟩ := float32Dot_mixed_of_certificate a b x y bx bys n hx hy hbx hby hc
  exact ⟨s, hv, he.forward⟩

end FP.Native
