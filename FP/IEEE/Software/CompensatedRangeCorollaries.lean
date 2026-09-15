import FP.IEEE.Software.CompensatedRangeCertificate
import FP.IEEE.Software.CompensatedDotRangeCertificate

/-! Real-decoding and paired-list entry points for automatic range proofs. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange FP.Range
open scoped BigOperators

theorem wordIn_lists_of_decoded (I : Interchange) [I.Valid]
    {bounds : List Interval} {xs : List I.Word} {ys : List ℝ}
    (hd : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains bounds ys) : List.Forall₂ (WordIn I) bounds xs := by
  induction hd generalizing bounds with
  | nil => cases hb; exact .nil
  | @cons w y xs ys hw hd ih =>
    cases hb with
    | cons hy hb => exact .cons (WordIn.of_decode I hw hy) (ih hb)

theorem compensatedSum_of_range_certificate (I : Interchange) [I.Valid]
    (bounds : List Interval) (xs : List I.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains bounds ys)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    CompensatedSumFinite I xs ∧ ∃ q : ℝ,
      I.decode? (compensatedSum I xs).value = some q ∧ r.resultInterval.Contains q ∧
      r.exactInterval.Contains ys.sum ∧ |q-ys.sum| ≤ (r.errorBound : ℝ) := by
  simpa only [wordListSum_cast I xs ys hd] using
    checkCompensatedSum_sound I (wordIn_lists_of_decoded I hd hb) hc

theorem compensatedDot_of_range_certificate (I : Interchange) [I.Valid]
    (A B : ℕ → Interval) (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (hA : ∀ i < n, (A i).Contains (x i)) (hB : ∀ i < n, (B i).Contains (y i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    CompensatedDotFinite I a b n ∧ ∃ q : ℝ,
      I.decode? (compensatedDot I a b n).value = some q ∧ r.resultInterval.Contains q ∧
      r.exactInterval.Contains (∑ i ∈ Finset.range n, x i*y i) ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ (r.errorBound : ℝ) := by
  simpa only [wordDotSum_cast I a b x y n ha hb] using
    checkCompensatedDot_sound I A B a b n
      (fun i hi => WordIn.of_decode I (ha i hi) (hA i hi))
      (fun i hi => WordIn.of_decode I (hb i hi) (hB i hi)) hc

theorem pairedWordIn_getD (I : Interchange) [I.Valid]
    {bounds : List (Interval × Interval)} {xs : List (I.Word × I.Word)}
    (hb : List.Forall₂ (fun J w => WordIn I J.1 w.1 ∧ WordIn I J.2 w.2) bounds xs)
    (i : ℕ) (hi : i < xs.length) :
    WordIn I (bounds[i]?.getD (.zero,.zero)).1 (xs[i]?.getD (0,0)).1 ∧
    WordIn I (bounds[i]?.getD (.zero,.zero)).2 (xs[i]?.getD (0,0)).2 := by
  induction hb generalizing i with
  | nil => simp at hi
  | cons h hb ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih i (by simpa using hi)

theorem checkCompensatedDotList_sound (I : Interchange) [I.Valid]
    (bounds : List (Interval × Interval)) (xs : List (I.Word × I.Word))
    (hb : List.Forall₂ (fun J w => WordIn I J.1 w.1 ∧ WordIn I J.2 w.2) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedDotList (.ofFormat I.format) bounds = some r) :
    CompensatedDotListFinite I xs ∧ ∃ q : ℝ,
      I.decode? (compensatedDotList I xs).value = some q ∧ r.resultInterval.Contains q ∧
      r.exactInterval.Contains ((xs.map (fun w => wordRat I w.1*wordRat I w.2)).sum : ℝ) ∧
      |q-((xs.map (fun w => wordRat I w.1*wordRat I w.2)).sum : ℝ)| ≤ (r.errorBound : ℝ) := by
  have hc' : checkCompensatedDot (.ofFormat I.format)
      (fun i => (bounds[i]?.getD (.zero,.zero)).1)
      (fun i => (bounds[i]?.getD (.zero,.zero)).2) xs.length = some r := by
    simpa only [checkCompensatedDotList,hb.length_eq] using hc
  simpa only [compensatedDotList,CompensatedDotListFinite,wordDotSum_pairList] using
    checkCompensatedDot_sound I _ _ (fun i => (xs[i]?.getD (0,0)).1)
      (fun i => (xs[i]?.getD (0,0)).2) xs.length
      (fun i hi => (pairedWordIn_getD I hb i hi).1)
      (fun i hi => (pairedWordIn_getD I hb i hi).2) hc'

theorem compensatedDotList_complete_of_range_certificate (I : Interchange) [I.Valid]
    (bounds : List (Interval × Interval)) (xs : List (I.Word × I.Word))
    (hb : List.Forall₂ (fun J w => WordIn I J.1 w.1 ∧ WordIn I J.2 w.2) bounds xs)
    {r : AccuracyCertificate} (hc : checkCompensatedDotList (.ofFormat I.format) bounds = some r) :
    ∃ c, compensatedDotList? I xs = some c :=
  compensatedDotList?_complete I xs (checkCompensatedDotList_sound I bounds xs hb hc).1

theorem compensatedSum_mixed_of_range_certificate (I : Interchange) [I.Valid] (bounds : List Interval) (xs : List I.Word) (ys : List ℝ)
    (hdec : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains bounds ys)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-ys.sum| ≤ I.format.unitRoundoff*|ys.sum|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff ys.length)^2*(ys.map (fun y => |y|)).sum+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff ys.length)*
            geomWeight I.format.unitRoundoff ys.length)+I.format.minSubnormal/2 :=
  compensatedSum_mixed_of_decoded I xs ys hdec
    (checkCompensatedSum_sound I (wordIn_lists_of_decoded I hdec hb) hc).1

theorem compensatedSum_gamma_of_range_certificate (I : Interchange) [I.Valid] (bounds : List Interval) (xs : List I.Word) (ys : List ℝ)
    (hdec : List.Forall₂ (fun w y => I.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains bounds ys)
    {r : AccuracyCertificate} (hc : checkCompensatedSum (.ofFormat I.format) bounds = some r) (hn : ys.length*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedSum I xs).value = some q ∧
      |q-ys.sum| ≤ I.format.unitRoundoff*|ys.sum|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff ys.length)^2*(ys.map (fun y => |y|)).sum+
          ys.length*(I.format.minSubnormal/2)/(1-ys.length*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 :=
  compensatedSum_gamma_of_decoded I xs ys hdec
    (checkCompensatedSum_sound I (wordIn_lists_of_decoded I hdec hb) hc).1 hn

theorem compensatedDot_mixed_of_range_certificate (I : Interchange) [I.Valid] (A B : ℕ → Interval) (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (hA : ∀ i < n, (A i).Contains (x i)) (hB : ∀ i < n, (B i).Contains (y i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ I.format.unitRoundoff*|∑ i ∈ Finset.range n, x i*y i|+
        (1+I.format.unitRoundoff)*((growth I.format.unitRoundoff (2*n))^2*FP.dotMass x y n+
          (I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*(geomWeight I.format.unitRoundoff (2*n)+n))+
            I.format.minSubnormal/2 :=
  compensatedDot_mixed_of_decoded I a b x y n ha hb
    (compensatedDot_of_range_certificate I A B a b x y n ha hb hA hB hc).1

theorem compensatedDot_gamma_of_range_certificate (I : Interchange) [I.Valid] (A B : ℕ → Interval) (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (hA : ∀ i < n, (A i).Contains (x i)) (hB : ∀ i < n, (B i).Contains (y i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) (hn : (2*n : ℕ)*I.format.unitRoundoff < 1) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      |q-∑ i ∈ Finset.range n, x i*y i| ≤ I.format.unitRoundoff*|∑ i ∈ Finset.range n, x i*y i|+
        (1+I.format.unitRoundoff)*((gamma I.format.unitRoundoff (2*n))^2*FP.dotMass x y n+
          3*n*(I.format.minSubnormal/2)/(1-(2*n : ℕ)*I.format.unitRoundoff)^2)+I.format.minSubnormal/2 :=
  compensatedDot_gamma_of_decoded I a b x y n ha hb
    (compensatedDot_of_range_certificate I A B a b x y n ha hb hA hB hc).1 hn

theorem compensatedDot_mixed_backward_of_range_certificate (I : Interchange) [I.Valid] (A B : ℕ → Interval) (a b : ℕ → I.Word) (x y : ℕ → ℝ) (n : ℕ)
    (ha : ∀ i < n, I.decode? (a i) = some (x i)) (hb : ∀ i < n, I.decode? (b i) = some (y i))
    (hA : ∀ i < n, (A i).Contains (x i)) (hB : ∀ i < n, (B i).Contains (y i))
    {r : AccuracyCertificate} (hc : checkCompensatedDot (.ofFormat I.format) A B n = some r) :
    ∃ q : ℝ, I.decode? (compensatedDot I a b n).value = some q ∧
      FP.MixedBackwardStable (I.format.unitRoundoff+(1+I.format.unitRoundoff)*(growth I.format.unitRoundoff (2*n))^2)
        ((1+I.format.unitRoundoff)*(I.format.minSubnormal/2)*(1+growth I.format.unitRoundoff (2*n))*
          (geomWeight I.format.unitRoundoff (2*n)+n)+I.format.minSubnormal/2) x y n q :=
  compensatedDot_mixed_backward I a b x y n ha hb
    (compensatedDot_of_range_certificate I A B a b x y n ha hb hA hB hc).1

end FP.IEEE.Software
