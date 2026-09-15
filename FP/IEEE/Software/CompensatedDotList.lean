import FP.IEEE.Software.CompensatedDotRange
import Mathlib.Data.List.OfFn

/-! Paired-list interfaces, with no truncation or inspected out-of-range inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open scoped BigOperators

abbrev CompensatedDotListFinite (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word)) : Prop :=
  CompensatedDotFinite I (fun i => (xs[i]?.getD (0,0)).1) (fun i => (xs[i]?.getD (0,0)).2) xs.length

private theorem sum_getD_map {α M : Type*} [AddCommMonoid M] (xs : List α) (d : α) (f : α → M) :
    (∑ i ∈ Finset.range xs.length, f (xs[i]?.getD d)) = (xs.map f).sum := by
  rw [← Fin.sum_univ_eq_sum_range,← List.sum_ofFn]
  congr 1
  calc
    _ = List.ofFn (fun i : Fin xs.length => f xs[i.val]) := by
      congr 1
      funext i
      simp
    _ = _ := List.ofFn_getElem_eq_map xs f

theorem wordDotSum_pairList (I : Interchange) (xs : List (I.Word × I.Word)) :
    wordDotSum I (fun i => (xs[i]?.getD (0,0)).1) (fun i => (xs[i]?.getD (0,0)).2) xs.length =
      (xs.map (fun p => wordRat I p.1*wordRat I p.2)).sum :=
  sum_getD_map xs (0,0) (fun p => wordRat I p.1*wordRat I p.2)

theorem wordDotAbsSum_pairList (I : Interchange) (xs : List (I.Word × I.Word)) :
    wordDotAbsSum I (fun i => (xs[i]?.getD (0,0)).1) (fun i => (xs[i]?.getD (0,0)).2) xs.length =
      (xs.map (fun p => |wordRat I p.1*wordRat I p.2|)).sum :=
  sum_getD_map xs (0,0) (fun p => |wordRat I p.1*wordRat I p.2|)

theorem compensatedDotList?_complete (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word))
    (h : CompensatedDotListFinite I xs) : ∃ r, compensatedDotList? I xs = some r :=
  compensatedDot?_complete I _ _ xs.length h

theorem compensatedDotList_mixed_of_finite (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word))
    (h : CompensatedDotListFinite I xs) :
    ∃ q : ℝ, I.decode? (compensatedDotList I xs).value = some q ∧
      |q-((xs.map (fun p => wordRat I p.1*wordRat I p.2)).sum : ℝ)| ≤
        I.format.unitRoundoff*|((xs.map (fun p => wordRat I p.1*wordRat I p.2)).sum : ℝ)|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*xs.length))^2*
          ((xs.map (fun p => |wordRat I p.1*wordRat I p.2|)).sum : ℝ)+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*xs.length))*
            (geomWeight I.format.unitRoundoff (2*xs.length)+xs.length))+I.format.minSubnormal/2 := by
  simpa only [compensatedDotList,wordDotSum_pairList,wordDotAbsSum_pairList] using
    compensatedDot_mixed_of_finite I _ _ xs.length h

theorem compensatedDotList_exact_of_zero_bound (I : Interchange) [I.Valid] (xs : List (I.Word × I.Word))
    (h : (compensatedDotList? I xs).map (fun r => r.errorBound) = some 0) :
    I.decode? (compensatedDotList I xs).value = some ((xs.map (fun p => wordRat I p.1*wordRat I p.2)).sum : ℝ) := by
  simpa only [compensatedDotList,wordDotSum_pairList] using compensatedDot_exact_of_zero_bound I _ _ xs.length h

end FP.IEEE.Software
