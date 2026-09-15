import FP.IEEE.Software.TotalReductionBounds

/-! A domain certificate supplies all intermediate range hypotheses. The result
is for the specified, zero-started, separately rounded multiply/add schedule. -/
namespace Examples
open FP FP.IEEE FP.IEEE.Software
open scoped BigOperators

private def unitBox : FP.Range.Interval := ⟨-1, 1⟩

theorem ieee32_dot_forward
    (a b : ℕ → fp32.Word) (x y : ℕ → ℝ)
    (ha : ∀ i < 5, fp32.decode? (a i) = some (x i))
    (hb : ∀ i < 5, fp32.decode? (b i) = some (y i))
    (hx : ∀ i < 5, (-1 : ℝ) ≤ x i ∧ x i ≤ 1)
    (hy : ∀ i < 5, (-1 : ℝ) ≤ y i ∧ y i ≤ 1) :
    ∃ z : ℝ, fp32.decode? (dot fp32 .nearestEven a b 5).value = some z ∧
      |z - ∑ i ∈ Finset.range 5, x i * y i| ≤
        growth binary32.unitRoundoff 10 * (∑ i ∈ Finset.range 5, |x i * y i|) +
          dotResidual binary32.unitRoundoff (binary32.minSubnormal / 2) 5 := by
  have hc : (FP.Range.checkDot (.ofFormat binary32)
      (fun _ => unitBox) (fun _ => unitBox) 5).isSome = true := by decide +kernel
  obtain ⟨enclosure, hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨z, hz, _, he⟩ := dot_mixed_of_certificate fp32 a b x y
    (fun _ => unitBox) (fun _ => unitBox) 5 ha hb
    (by simpa [unitBox, FP.Range.Interval.Contains] using hx)
    (by simpa [unitBox, FP.Range.Interval.Contains] using hy) hc
  exact ⟨z, hz, he.forward⟩

end Examples
