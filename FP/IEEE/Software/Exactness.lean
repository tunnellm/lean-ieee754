import FP.IEEE.Software.Widening
import FP.IEEE.Spec.Directed

/-! Representable range bounds and exactness certificates for actual result words. -/
namespace FP.IEEE.Software
open Interchange

def flagsClear (f : Flags) : Bool :=
  !(f .invalid || f .divideByZero || f .overflow || f .underflow || f .inexact)

theorem flagsClear_iff (f : Flags) : flagsClear f = true ↔ f = Flags.empty := by
  simp only [flagsClear, Bool.not_eq_true', Bool.or_eq_false_iff]
  constructor
  · rintro ⟨⟨⟨⟨hi, hd⟩, ho⟩, hu⟩, hx⟩
    funext e; cases e <;> assumption
  · intro h; subst f; simp [Flags.empty]


theorem representable_le_max (F : Format) (x : ℝ) (hx : F.Representable x) : |x| ≤ F.maxFinite := by
  obtain ⟨m, e, _, he, hm, rfl⟩ := hx
  have hi : |m| < (2 : ℤ)^F.precision := by exact_mod_cast hm
  have hi' : |m| ≤ (2 : ℤ)^F.precision - 1 := by omega
  have hr : |(m : ℝ)| ≤ (2 : ℝ)^F.precision - 1 := by exact_mod_cast hi'
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^e)]
  exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans
    (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) he)
      (by have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := F.precision); linarith))

theorem pow_emax_le_maxFinite (F : Format) : (2 : ℚ)^F.emax ≤ maxFinite F := by
  have he : (2 : ℚ)^F.emax = (2 : ℚ)^F.fractionBits * (2 : ℚ)^(F.emax - F.fractionBits) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; congr 1; omega
  rw [he, maxFinite, pow_succ]
  have hp : (1 : ℚ) ≤ 2^F.fractionBits := one_le_pow₀ (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private theorem roundInt_abs_le_of_le (mode : RoundingMode) (x : ℚ) (n : ℕ)
    (hx : |x| ≤ (n : ℚ)) : |roundInt mode x| ≤ (n : ℤ) := by
  have he := roundInt_error_lt_one mode x
  have ht := abs_add_le ((roundInt mode x : ℚ) - x) x
  rw [sub_add_cancel] at ht
  have hh : |(roundInt mode x : ℚ)| < (n : ℚ)+1 := by linarith
  have hi : |roundInt mode x| < (n : ℤ)+1 := by exact_mod_cast hh
  omega

/-- An exact input inside the finite range cannot overflow in any mode. -/
theorem noOverflow_of_abs_le_max (F : Format) (mode : RoundingMode) (q : ℚ)
    (hq : |q| ≤ maxFinite F) : overflowWithMode F mode q = false := by
  by_cases hz : q = 0
  · subst q
    simp [overflowWithMode, precisionRoundWithMode, not_lt.mpr (maxFinite_pos F).le]
  have hl : Int.log 2 |q| ≤ F.emax := by
    have h := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) (abs_pos.mpr hz)).mp
      (hq.trans_lt (maxFinite_lt_next F))
    omega
  rcases hl.lt_or_eq with hl | hl
  · have hb := precisionRound_abs_upper F mode q
    have hp : (2 : ℚ)^(Int.log 2 |q| + 1) ≤ (2 : ℚ)^F.emax :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    simpa [overflowWithMode, not_lt] using hb.trans (hp.trans (pow_emax_le_maxFinite F))
  · let h := (2 : ℚ)^(F.emax - F.fractionBits)
    have hp : 0 < h := by dsimp [h]; positivity
    have hn : (0 : ℕ) < 2^F.precision := by positivity
    have hncast : ((2^F.precision - 1 : ℕ) : ℚ) = (2 : ℚ)^F.precision - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have hscaled : |q / h| ≤ ((2^F.precision - 1 : ℕ) : ℚ) := by
      rw [hncast, abs_div, abs_of_pos hp, div_le_iff₀ hp]
      exact hq
    have hi := roundInt_abs_le_of_le mode (q/h) (2^F.precision - 1) hscaled
    have hr : |(roundInt mode (q/h) : ℚ)| ≤ (2 : ℚ)^F.precision - 1 := by
      rw [← hncast]; exact_mod_cast hi
    have hb : |precisionRoundWithMode F mode q| ≤ maxFinite F := by
      simp only [precisionRoundWithMode, hl]
      rw [abs_mul, abs_of_pos hp]
      exact mul_le_mul_of_nonneg_right hr hp.le
    simpa [overflowWithMode, not_lt] using hb

/-- Every exactly representable input rounds to itself without exceptions. -/
theorem roundWithMode_exact (I : Interchange) [I.Valid] (mode : RoundingMode) (q : ℚ)
    (sign : Bool) (hq : I.format.Representable (q : ℝ)) :
    I.decode? (roundWithMode I mode q sign).value = some (q : ℝ) ∧
    (roundWithMode I mode q sign).flags = Flags.empty := by
  have hb : |q| ≤ maxFinite I.format := by
    have h := representable_le_max I.format (q : ℝ) hq
    rw [← maxFinite_cast] at h; exact_mod_cast h
  have ho := noOverflow_of_abs_le_max I.format mode q hb
  have he := scaledRound_exact I.format mode q hq
  constructor
  · have h := (roundWithMode_spec I mode q sign).finite (by simpa [← overflowWithMode_spec] using ho)
    rw [← scaledRound_cast, he] at h
    exact h
  · funext e
    cases e <;> simp [roundWithMode, roundingFlags, ho, he, Flags.empty]

theorem roundWithMode_exact_of_no_flags (I : Interchange) [I.Valid] (mode : RoundingMode)
    (q : ℚ) (sign : Bool) (hf : (roundWithMode I mode q sign).flags = Flags.empty) :
    I.decode? (roundWithMode I mode q sign).value = some (q : ℝ) := by
  have hi := congrFun hf Exception.inexact
  have he : overflowWithMode I.format mode q = false ∧ scaledRound I.format mode q = q := by
    simpa [roundWithMode, roundingFlags, Flags.empty] using hi
  have h := (roundWithMode_spec I mode q sign).finite (by simpa [← overflowWithMode_spec] using he.1)
  simpa [← scaledRound_cast, he.2] using h

/-- Every finite value lies on the common least-subnormal lattice. -/
theorem representable_min_lattice (F : Format) (x : ℝ) (hx : F.Representable x) :
    ∃ k : ℤ, x = (k : ℝ)*F.minSubnormal := by
  obtain ⟨m,e,hl,_,_,rfl⟩ := hx
  refine ⟨m * (2 : ℤ)^(e - (F.emin-F.fractionBits)).toNat, ?_⟩
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (by omega), Format.minSubnormal,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

theorem representable_gap (F : Format) (x y : ℝ) (hx : F.Representable x)
    (hy : F.Representable y) (hxy : x < y) : F.minSubnormal ≤ y-x := by
  obtain ⟨a, rfl⟩ := representable_min_lattice F x hx
  obtain ⟨b, rfl⟩ := representable_min_lattice F y hy
  have hp : 0 < F.minSubnormal := by unfold Format.minSubnormal; positivity
  have hab : (a : ℝ) < b := (mul_lt_mul_iff_left₀ hp).mp hxy
  have hi : a < b := by exact_mod_cast hab
  have hd : (1 : ℝ) ≤ (b : ℝ)-a := by exact_mod_cast (show (1 : ℤ) ≤ b-a by omega)
  nlinarith
end FP.IEEE.Software
