import FP.IEEE.Software.CompensatedRangeCorollaries

/-! Kernel certificates for whole domains, subnormal losses, and rejected bounds. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace FP.IEEE.Software.Tests
open Interchange FP.Range
open scoped BigOperators

private theorem rat_lt_real {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by exact_mod_cast h

private def unitBox : Interval := ⟨-1,1⟩
private def boxes : List Interval := List.replicate 5 unitBox

private def sumBox32 : AccuracyCertificate :=
  (checkCompensatedSum (.ofFormat binary32) boxes).getD .zero
private def sumBox64 : AccuracyCertificate :=
  (checkCompensatedSum (.ofFormat binary64) boxes).getD .zero
private def dotBox32 : AccuracyCertificate :=
  (checkCompensatedDot (.ofFormat binary32) (fun _ => unitBox) (fun _ => unitBox) 5).getD .zero
private def dotBox64 : AccuracyCertificate :=
  (checkCompensatedDot (.ofFormat binary64) (fun _ => unitBox) (fun _ => unitBox) 5).getD .zero

example : checkCompensatedSum (.ofFormat binary32) boxes = some sumBox32 ∧
    sumBox32.errorBound < 1/100000 ∧
    checkCompensatedSum (.ofFormat binary64) boxes = some sumBox64 ∧
    sumBox64.errorBound < 1/1000000000000 := by decide +kernel

example : checkCompensatedDot (.ofFormat binary32) (fun _ => unitBox) (fun _ => unitBox) 5 = some dotBox32 ∧
    dotBox32.errorBound < 1/100000 ∧
    checkCompensatedDot (.ofFormat binary64) (fun _ => unitBox) (fun _ => unitBox) 5 = some dotBox64 ∧
    dotBox64.errorBound < 1/1000000000000 := by decide +kernel

/-- One closed certificate proves accuracy for every list in this domain. -/
example (xs : List fp32.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => fp32.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains boxes ys) :
    ∃ q : ℝ, fp32.decode? (compensatedSum fp32 xs).value = some q ∧
      |q-ys.sum| < 1/100000 := by
  obtain ⟨_,q,hq,_,_,he⟩ := compensatedSum_of_range_certificate fp32 boxes xs ys hd hb
    (r := sumBox32) (by decide +kernel)
  have hB : (sumBox32.errorBound : ℝ) < 1/100000 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      rat_lt_real (show sumBox32.errorBound < 1/100000 from by decide +kernel)
  exact ⟨q,hq,he.trans_lt hB⟩

example (xs : List fp64.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => fp64.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains boxes ys) :
    ∃ q : ℝ, fp64.decode? (compensatedSum fp64 xs).value = some q ∧
      |q-ys.sum| < 1/1000000000000 := by
  obtain ⟨_,q,hq,_,_,he⟩ := compensatedSum_of_range_certificate fp64 boxes xs ys hd hb
    (r := sumBox64) (by decide +kernel)
  have hB : (sumBox64.errorBound : ℝ) < 1/1000000000000 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      rat_lt_real (show sumBox64.errorBound < 1/1000000000000 from by decide +kernel)
  exact ⟨q,hq,he.trans_lt hB⟩

example (a b : ℕ → fp32.Word) (x y : ℕ → ℝ)
    (ha : ∀ i < 5, fp32.decode? (a i) = some (x i)) (hb : ∀ i < 5, fp32.decode? (b i) = some (y i))
    (hA : ∀ i < 5, unitBox.Contains (x i)) (hB : ∀ i < 5, unitBox.Contains (y i)) :
    ∃ q : ℝ, fp32.decode? (compensatedDot fp32 a b 5).value = some q ∧
      |q-∑ i ∈ Finset.range 5, x i*y i| < 1/100000 := by
  obtain ⟨_,q,hq,_,_,he⟩ := compensatedDot_of_range_certificate fp32 _ _ a b x y 5 ha hb hA hB
    (r := dotBox32) (by decide +kernel)
  have hR : (dotBox32.errorBound : ℝ) < 1/100000 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      rat_lt_real (show dotBox32.errorBound < 1/100000 from by decide +kernel)
  exact ⟨q,hq,he.trans_lt hR⟩

example (a b : ℕ → fp64.Word) (x y : ℕ → ℝ)
    (ha : ∀ i < 5, fp64.decode? (a i) = some (x i)) (hb : ∀ i < 5, fp64.decode? (b i) = some (y i))
    (hA : ∀ i < 5, unitBox.Contains (x i)) (hB : ∀ i < 5, unitBox.Contains (y i)) :
    ∃ q : ℝ, fp64.decode? (compensatedDot fp64 a b 5).value = some q ∧
      |q-∑ i ∈ Finset.range 5, x i*y i| < 1/1000000000000 := by
  obtain ⟨_,q,hq,_,_,he⟩ := compensatedDot_of_range_certificate fp64 _ _ a b x y 5 ha hb hA hB
    (r := dotBox64) (by decide +kernel)
  have hR : (dotBox64.errorBound : ℝ) < 1/1000000000000 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      rat_lt_real (show dotBox64.errorBound < 1/1000000000000 from by decide +kernel)
  exact ⟨q,hq,he.trans_lt hR⟩

/-- Invalid used inputs are rejected; unused interval functions are not inspected. -/
example : checkCompensatedSum (.ofFormat binary32) [⟨1,0⟩] = none ∧
    checkCompensatedDot (.ofFormat binary64) (fun _ => ⟨1,0⟩) (fun _ => unitBox) 1 = none ∧
    checkCompensatedSum (.ofFormat binary32) [] = some .zero ∧
    checkCompensatedDot (.ofFormat binary64) (fun _ => ⟨1,0⟩) (fun _ => ⟨2,0⟩) 0 = some .zero := by
  decide +kernel

example : checkRound (.ofFormat binary32) (.singleton (Params.ofFormat binary32).threshold) = none ∧
    checkRound (.ofFormat binary64) (.singleton (Params.ofFormat binary64).threshold) = none := by decide +kernel

private def points (I : Interchange) (xs : List I.Word) : List Interval :=
  xs.map (fun w => .singleton (wordRat I w))
private def pairPoints (I : Interchange) (xs : List (I.Word × I.Word)) : List (Interval × Interval) :=
  xs.map (fun w => (.singleton (wordRat I w.1), .singleton (wordRat I w.2)))

/-- Range certification supplies measured enclosures for every input in the domain. -/
example (xs : List fp32.Word) (ys : List ℝ)
    (hd : List.Forall₂ (fun w y => fp32.decode? w = some y) xs ys)
    (hb : List.Forall₂ Interval.Contains boxes ys) :
    ∃ J, compensatedEnclosure? fp32 xs = some J ∧ J.Contains (wordListSum fp32 xs : ℝ) :=
  compensatedSum_enclosure_of_range_certificate fp32
    (wordIn_lists_of_decoded fp32 hd hb) (r := sumBox32) (by decide +kernel)

private def pairBoxes : List (Interval × Interval) := List.replicate 5 (unitBox,unitBox)
private def pairBox64 : AccuracyCertificate :=
  (checkCompensatedDotList (.ofFormat binary64) pairBoxes).getD .zero

example (xs : List (fp64.Word × fp64.Word))
    (hb : List.Forall₂ (fun J w => WordIn fp64 J.1 w.1 ∧ WordIn fp64 J.2 w.2) pairBoxes xs) :
    ∃ c, compensatedDotList? fp64 xs = some c :=
  compensatedDotList_complete_of_range_certificate fp64 pairBoxes xs hb
    (r := pairBox64) (by decide +kernel)

example (J : Interval) : ¬ WordIn fp32 J 0x7fc00123 ∧ ¬ WordIn fp64 J 0x7ff0000000000000 := by
  constructor
  · intro h
    have hn : (Datum.decode fp32 0x7fc00123).isFinite = false := by decide +kernel
    have hh := h.1
    rw [hn] at hh
    exact Bool.noConfusion hh
  · intro h
    have hn : (Datum.decode fp64 0x7ff0000000000000).isFinite = false := by decide +kernel
    have hh := h.1
    rw [hn] at hh
    exact Bool.noConfusion hh

/-- Signed zeros, least subnormals, and large cancellation are accepted. -/
example : (checkCompensatedSum (.ofFormat binary32) (points fp32 [0x80000000,1,1,0x80000001])).isSome = true ∧
    (checkCompensatedSum (.ofFormat binary64) (points fp64 [0x8000000000000000,1,1,0x8000000000000001])).isSome = true ∧
    (checkCompensatedSum (.ofFormat binary32) (points fp32 [0x4c000000,0x3f800000,0xcc000000])).isSome = true ∧
    (checkCompensatedSum (.ofFormat binary64) (points fp64 [0x4350000000000000,0x3ff0000000000000,0xc350000000000000])).isSome = true := by decide +kernel

/-- Dot2 accepts a residual underflow that the exact TwoProduct certificate rejects. -/
example : (checkCompensatedDotList (.ofFormat binary32) (pairPoints fp32 [(1,0x3f000000)])).isSome = true ∧
    (checkCompensatedDotList (.ofFormat binary64) (pairPoints fp64 [(1,0x3fe0000000000000)])).isSome = true ∧
    (certifiedTwoProduct? fp32 1 0x3f000000).isNone = true ∧
    (certifiedTwoProduct? fp64 1 0x3fe0000000000000).isNone = true := by decide +kernel

/-- Conservative rejection is not a proof of overflow. -/
example : checkCompensatedSum (.ofFormat binary32) (points fp32 [0x7f7fffff]) = none ∧
    CompensatedSumFinite fp32 [0x7f7fffff] ∧
    checkCompensatedSum (.ofFormat binary64) (points fp64 [0x7fefffffffffffff]) = none ∧
    CompensatedSumFinite fp64 [0x7fefffffffffffff] := by decide +kernel

/-- Previously established high/bvirt/final failures cannot be certified. -/
example : checkCompensatedSum (.ofFormat binary32) (points fp32 [0x7f7fffff,0x7f7fffff]) = none ∧
    checkCompensatedSum (.ofFormat binary32) (points fp32 [0xf3c00000,0x7f7fffff]) = none ∧
    checkCompensatedSum (.ofFormat binary32) (points fp32 [0x7f7fffff,0x72800000,0x72800000]) = none ∧
    checkCompensatedSum (.ofFormat binary64) (points fp64 [0xfca8000000000000,0x7fefffffffffffff]) = none ∧
    checkCompensatedSum (.ofFormat binary64) (points fp64 [0x7fefffffffffffff,0x7c80000000000000,0x7c80000000000000]) = none := by decide +kernel

example : checkCompensatedDotList (.ofFormat binary32) (pairPoints fp32 [(0x7f7fffff,0x40000000)]) = none ∧
    checkCompensatedDotList (.ofFormat binary64) (pairPoints fp64 [(0x7fefffffffffffff,0x4000000000000000)]) = none ∧
    checkCompensatedFinish (.ofFormat binary32) ⟨.singleton (Params.ofFormat binary32).threshold,.zero⟩ = none := by decide +kernel

/-- A valid high path does not excuse a correction or final-addition failure. -/
example : checkCompensatedStep (.ofFormat binary32)
      ⟨.zero,.singleton (Params.ofFormat binary32).threshold⟩ .zero = none ∧
    checkCompensatedDotStep (.ofFormat binary64)
      ⟨.zero,.singleton (Params.ofFormat binary64).threshold⟩ .zero .zero = none ∧
    checkCompensatedStep (.ofFormat binary32)
      ⟨.singleton (wordRat fp32 0x7f7ffffe),.singleton (wordRat fp32 0x7f7fffff)⟩
      (.singleton (wordRat fp32 0x73000000)) = none ∧
    checkCompensatedDotStep (.ofFormat binary64)
      ⟨.singleton (wordRat fp64 0x7feffffffffffffe),.singleton (wordRat fp64 0x7fefffffffffffff)⟩
      (.singleton (wordRat fp64 0x7c90000000000000)) (.singleton 1) = none := by decide +kernel

end FP.IEEE.Software.Tests
