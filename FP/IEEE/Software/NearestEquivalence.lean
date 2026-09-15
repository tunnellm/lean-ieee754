import FP.IEEE.Software.TotalRound

/-! Equivalence of the midpoint overflow threshold and the IEEE
unbounded-exponent test, including both signs of the exact midpoint. -/
namespace FP.IEEE.Software

private theorem even_boundary (n : ℕ) (hn : (n : ℤ) % 2 = 0) :
    roundInt .nearestEven ((n : ℚ) - 1 / 2) = n ∧
    roundInt .nearestEven (-((n : ℚ) - 1 / 2)) = -(n : ℤ) := by
  have hp : (n : ℚ) - 1 / 2 = ((n : ℤ) - 1 : ℤ) + 1 / 2 := by push_cast; ring
  have hm : -((n : ℚ) - 1 / 2) = (-(n : ℤ) : ℤ) + 1 / 2 := by push_cast; ring
  rw [hp, roundInt_even_midpoint]
  constructor
  · omega
  · rw [← hp, hm, roundInt_even_midpoint]
    omega

/-- The open interval that rounds strictly inside an even integer boundary.
Strictness at the midpoint is essential for overflow. -/
theorem roundInt_even_abs_lt (n : ℕ) (hn : (n : ℤ) % 2 = 0) (hp : 0 < n) (x : ℚ) :
    |(roundInt .nearestEven x : ℚ)| < n ↔ |x| < (n : ℚ) - 1 / 2 := by
  have he := roundInt_nearest_error .nearestEven (Or.inl rfl) x
  have ht := abs_add_le ((roundInt .nearestEven x : ℚ) - x) x
  rw [sub_add_cancel] at ht
  constructor
  · intro h
    have hi : |roundInt .nearestEven x| < (n : ℤ) := by exact_mod_cast h
    have hb : |(roundInt .nearestEven x : ℚ)| ≤ (n : ℚ) - 1 := by
      exact_mod_cast (show |roundInt .nearestEven x| ≤ (n : ℤ) - 1 by omega)
    have ht' := abs_add_le (x - (roundInt .nearestEven x : ℚ)) (roundInt .nearestEven x : ℚ)
    rw [sub_add_cancel, abs_sub_comm] at ht'
    have hx : |x| ≤ (n : ℚ) - 1 / 2 := by linarith
    rcases hx.lt_or_eq with hlt | heq
    · exact hlt
    · have hnq : (0 : ℚ) ≤ (n : ℚ) - 1 / 2 := by
        have : (1 : ℚ) ≤ n := by exact_mod_cast hp
        linarith
      obtain ⟨hbpos, hbneg⟩ := even_boundary n hn
      rcases (abs_eq hnq).mp heq with hpos | hneg
      · rw [hpos, hbpos] at h
        simp at h
      · rw [hneg, hbneg] at h
        simp at h
  · intro h
    linarith

private theorem binade_scale (f : ℕ) (e : ℤ) :
    (2 : ℚ)^f * (2 : ℚ)^(e - f) = (2 : ℚ)^e := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  omega

private theorem binade_next (f : ℕ) (e : ℤ) :
    (2 : ℚ)^(f + 1) * (2 : ℚ)^(e - f) = (2 : ℚ)^(e + 1) := by
  rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, binade_scale,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp

private theorem range_bounds (F : Format) :
    (2 : ℚ)^F.emax ≤ maxFinite F ∧
    (2 : ℚ)^F.emax < overflowThreshold F ∧
    overflowThreshold F < (2 : ℚ)^(F.emax + 1) := by
  have hp : (1 : ℚ) ≤ 2^F.fractionBits := one_le_pow₀ (by norm_num)
  have hq : (0 : ℚ) < 2^(F.emax - F.fractionBits) := by positivity
  have hb := binade_scale F.fractionBits F.emax
  have hn := binade_next F.fractionBits F.emax
  unfold maxFinite overflowThreshold
  rw [← hb, ← hn, pow_succ]
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem precisionRound_abs_upper (F : Format) (mode : RoundingMode) (x : ℚ) :
    |precisionRoundWithMode F mode x| ≤ (2 : ℚ)^(Int.log 2 |x| + 1) := by
  let h := (2 : ℚ)^(Int.log 2 |x| - F.fractionBits)
  have hp : 0 < h := by dsimp [h]; positivity
  have hs : (2 : ℚ)^(F.fractionBits + 1) * h = (2 : ℚ)^(Int.log 2 |x| + 1) :=
    binade_next F.fractionBits (Int.log 2 |x|)
  have hi : |x / h| < (2 : ℚ)^(F.fractionBits + 1) := by
    rw [abs_div, abs_of_pos hp, div_lt_iff₀ hp, hs]
    exact Int.lt_zpow_succ_log_self (by norm_num) |x|
  have hm := roundInt_abs_le mode (x / h) (2^(F.fractionBits + 1)) (by exact_mod_cast hi)
  have hr : |(roundInt mode (x / h) : ℚ)| ≤ (2 : ℚ)^(F.fractionBits + 1) := by exact_mod_cast hm
  change |(roundInt mode (x / h) : ℚ) * h| ≤ _
  rw [abs_mul, abs_of_pos hp, ← hs]
  exact mul_le_mul_of_nonneg_right hr hp.le

/-- The IEEE unbounded-exponent overflow test is exactly the old nearest-even
midpoint threshold, for every rational input, including signed ties. -/
theorem overflowWithMode_even_iff (F : Format) (x : ℚ) :
    overflowWithMode F .nearestEven x = true ↔ ¬ |x| < overflowThreshold F := by
  obtain ⟨hmax, hlow, hhigh⟩ := range_bounds F
  by_cases hx : x = 0
  · subst x
    have hp := maxFinite_pos F
    have ht : 0 < overflowThreshold F := (show (0 : ℚ) < 2^F.emax by positivity).trans hlow
    simp [overflowWithMode, precisionRoundWithMode, not_lt.mpr hp.le, ht]
  let l := Int.log 2 |x|
  have hxlow : (2 : ℚ)^l ≤ |x| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
  have hxhigh : |x| < (2 : ℚ)^(l + 1) := Int.lt_zpow_succ_log_self (by norm_num) |x|
  rcases lt_trichotomy l F.emax with hl | he | hg
  · have hstep : (2 : ℚ)^(l + 1) ≤ (2 : ℚ)^F.emax :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hr := precisionRound_abs_upper F .nearestEven x
    have hn : ¬ maxFinite F < |precisionRoundWithMode F .nearestEven x| := by
      change |precisionRoundWithMode F .nearestEven x| ≤ (2 : ℚ)^(l + 1) at hr
      linarith
    have ht : |x| < overflowThreshold F := by linarith
    simp only [overflowWithMode, decide_eq_true_eq, hn, ht, not_true_eq_false]
  · have he' : Int.log 2 |x| = F.emax := he
    have hp : (0 : ℚ) < 2^(F.emax - F.fractionBits) := by positivity
    have hn : ((2^(F.fractionBits + 1) : ℕ) : ℤ) % 2 = 0 := by
      push_cast
      rw [pow_succ]
      omega
    have hi := roundInt_even_abs_lt (2^(F.fractionBits + 1)) hn (by positivity)
      (x / (2 : ℚ)^(F.emax - F.fractionBits))
    have hi' : |(roundInt .nearestEven (x / (2 : ℚ)^(F.emax - F.fractionBits)) : ℚ)| <
        (2 : ℚ)^(F.fractionBits + 1) ↔ |x| < overflowThreshold F := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, abs_div, abs_of_pos hp,
        div_lt_iff₀ hp, overflowThreshold] using hi
    have hdisc : (2 : ℚ)^(F.fractionBits + 1) - 1 <
        |(roundInt .nearestEven (x / (2 : ℚ)^(F.emax - F.fractionBits)) : ℚ)| ↔
        ¬ |(roundInt .nearestEven (x / (2 : ℚ)^(F.emax - F.fractionBits)) : ℚ)| <
          (2 : ℚ)^(F.fractionBits + 1) := by
      have h : ∀ z : ℤ, (2 : ℤ)^(F.fractionBits + 1) - 1 < |z| ↔
          ¬ |z| < (2 : ℤ)^(F.fractionBits + 1) := by intro z; omega
      exact_mod_cast h (roundInt .nearestEven (x / (2 : ℚ)^(F.emax - F.fractionBits)))
    simp only [overflowWithMode, decide_eq_true_eq, precisionRoundWithMode, he', maxFinite,
      abs_mul, abs_of_pos hp, mul_lt_mul_iff_left₀ hp, hdisc, hi']
  · have hstep : (2 : ℚ)^(F.emax + 1) ≤ (2 : ℚ)^l :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hr := precisionRound_abs_lower F .nearestEven x hx
    have hm := maxFinite_lt_next F
    have hb : maxFinite F < |precisionRoundWithMode F .nearestEven x| := by
      change (2 : ℚ)^l ≤ |precisionRoundWithMode F .nearestEven x| at hr
      linarith
    have ht : ¬ |x| < overflowThreshold F := by linarith
    simp only [overflowWithMode, decide_eq_true_eq, hb, ht, not_false_eq_true]

/-- Exact equality of the two total interfaces: result bits and every flag.
The old threshold-based API and the new all-mode API are interchangeable. -/
theorem roundWithMode_even_eq (I : Interchange) (x : ℚ) (zeroSign : Bool) :
    roundWithMode I .nearestEven x zeroSign = roundNearest I x zeroSign := by
  have hc := overflowWithMode_even_iff I.format x
  by_cases h : |x| < overflowThreshold I.format
  · have ho : overflowWithMode I.format .nearestEven x = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      exact (hc.mp hh) h
    unfold roundWithMode roundNearest
    simp only [ho, Bool.false_eq_true, not_false_eq_true, dif_neg, h, dif_pos]
    congr 1
    funext e
    cases e <;> simp only [roundingFlags, ho, Bool.false_or, Bool.not_false, Bool.true_and,
      tinyWithMode_even] <;> rfl
  · have ho := hc.mpr h
    unfold roundWithMode roundNearest
    simp only [ho, dif_pos, h]
    congr 1
    funext e
    cases e <;> simp only [roundingFlags, ho, Bool.true_or, Bool.not_true, Bool.false_and] <;> rfl

/-- Unconditional finite projection, including overflow, for the new endpoint. -/
theorem roundWithMode_even_projection (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool) :
    (Interchange.Datum.decode I (roundWithMode I .nearestEven x zeroSign).value).toRat? =
      roundNearest? I.format x := by
  rw [roundWithMode_even_eq]
  exact roundNearest_projection I x zeroSign

/-- Real-contract overflow equivalence on exact rational inputs. -/
theorem overflow_even_real_iff (F : Format) (x : ℚ) :
    Spec.OverflowWithMode F .nearestEven (x : ℝ) ↔ ¬ |(x : ℝ)| < F.overflowThreshold := by
  rw [← overflowWithMode_spec, overflowWithMode_even_iff, ← overflowThreshold_cast]
  have h := Rat.cast_lt (K := ℝ) (p := |x|) (q := overflowThreshold F)
  simpa only [Rat.cast_abs] using (not_congr h).symm

/-- The new word endpoint has exactly the original real finite projection. -/
theorem roundWithMode_even_cast (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool) :
    I.decode? (roundWithMode I .nearestEven x zeroSign).value = I.format.round? (x : ℝ) := by
  rw [roundWithMode_even_eq]
  exact (roundNearest_spec I x zeroSign).value

/-- The sharper nearest-even mixed bound transfers to actual result encodings. -/
theorem roundWithMode_even_mixed_error (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool)
    (ho : overflowWithMode I.format .nearestEven x = false) :
    ∃ y : ℝ, I.decode? (roundWithMode I .nearestEven x zeroSign).value = some y ∧
      |y - (x : ℝ)| ≤ I.format.unitRoundoff * |(x : ℝ)| + I.format.minSubnormal / 2 := by
  refine ⟨I.format.roundFinite (x : ℝ), ?_, I.format.roundFinite_mixed_error (x : ℝ)⟩
  exact (roundWithMode_spec I .nearestEven x zeroSign).finite
    (by simpa [← overflowWithMode_spec] using ho)

/-- The original pure relative model transfers under its original range condition. -/
theorem roundWithMode_even_relativeError (I : Interchange) [I.Valid] (x : ℚ) (zeroSign : Bool)
    (hx : I.format.Safe (x : ℝ)) :
    ∃ y : ℝ, I.decode? (roundWithMode I .nearestEven x zeroSign).value = some y ∧
      FP.RelativeError I.format.unitRoundoff (x : ℝ) y := by
  refine ⟨I.format.roundFinite (x : ℝ), ?_, I.format.roundFinite_relativeError hx⟩
  rw [roundWithMode_even_cast]
  exact I.format.round?_eq_of_safe hx

end FP.IEEE.Software
