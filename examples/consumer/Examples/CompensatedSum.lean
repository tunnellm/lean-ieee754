import FP.IEEE.Software.CompensatedRangeCorollaries

/-! A single rational certificate proves an absolute fp64 accuracy bound for
every five-element input list in [-1, 1], including subnormal inputs. -/
namespace Examples
open FP.IEEE FP.IEEE.Software FP.Range

private def boxes : List Interval := List.replicate 5 ⟨-1, 1⟩

private def certificate : AccuracyCertificate :=
  (checkCompensatedSum (.ofFormat binary64) boxes).getD .zero

private theorem cast_lt {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by
  exact_mod_cast h

theorem ieee64_compensated_sum_accuracy (xs : List fp64.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => fp64.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains (List.replicate 5 ⟨-1, 1⟩) ys) :
    ∃ q : ℝ, fp64.decode? (compensatedSum fp64 xs).value = some q ∧
      |q - ys.sum| < 1 / 1000000000000 := by
  obtain ⟨_, q, hq, _, _, he⟩ := compensatedSum_of_range_certificate fp64 boxes xs ys hd hb
    (r := certificate) (by decide +kernel)
  have hB : (certificate.errorBound : ℝ) < 1 / 1000000000000 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      cast_lt (show certificate.errorBound < 1 / 1000000000000 from by decide +kernel)
  exact ⟨q, hq, he.trans_lt hB⟩

end Examples
