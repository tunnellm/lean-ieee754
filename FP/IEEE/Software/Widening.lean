import FP.IEEE.Software.Conversion

/-! Exact binary32-to-binary64 finite widening in every rounding mode. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

theorem representable_mono (S D : Format) (x : ℝ)
    (hl : D.emin - D.fractionBits ≤ S.emin - S.fractionBits)
    (hu : S.emax - S.fractionBits ≤ D.emax - D.fractionBits)
    (hp : S.precision ≤ D.precision) (hx : S.Representable x) : D.Representable x := by
  obtain ⟨m, e, helo, hehi, hm, hv⟩ := hx
  exact ⟨m, e, hl.trans helo, hehi.trans hu,
    hm.trans_le (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp), hv⟩

theorem rat_representable_of_decode (S : Interchange) [S.Valid] (w : S.Word) (q : ℚ)
    (h : (Datum.decode S w).toRat? = some q) : S.format.Representable (q : ℝ) := by
  have hv := Datum.toRat?_decode S w
  rw [h] at hv
  simp only [Option.map_some] at hv
  unfold Interchange.decode? at hv
  split_ifs at hv with hf
  · rw [Option.some.inj hv]
    exact S.value_representable w hf

theorem representable_abs_lt_next (F : Format) (x : ℝ) (hx : F.Representable x) :
    |x| < (2 : ℝ)^(F.emax + 1) := by
  obtain ⟨m, e, _, he, hm, rfl⟩ := hx
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^e)]
  calc
    _ < (2 : ℝ)^F.precision * (2 : ℝ)^e := mul_lt_mul_of_pos_right hm (by positivity)
    _ ≤ (2 : ℝ)^F.precision * (2 : ℝ)^(F.emax - F.fractionBits) :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) he) (by positivity)
    _ = _ := by
      rw [Format.precision, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring

theorem noOverflow_of_abs_lt_pow (F : Format) (mode : RoundingMode) (q : ℚ) (e : ℤ)
    (hq : |q| < (2 : ℚ)^e) (he : (2 : ℚ)^e ≤ maxFinite F) :
    overflowWithMode F mode q = false := by
  by_cases hz : q = 0
  · subst q
    have hp := maxFinite_pos F
    simp [overflowWithMode, precisionRoundWithMode, not_lt.mpr hp.le]
  have hl : Int.log 2 |q| < e :=
    (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hz)).mp hq
  have hu := precisionRound_abs_upper F mode q
  have hstep : (2 : ℚ)^(Int.log 2 |q| + 1) ≤ (2 : ℚ)^e :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  simp only [overflowWithMode, decide_eq_false_iff_not, not_lt]
  exact hu.trans (hstep.trans he)

/-- Every finite binary32 encoding widens exactly, with no newly raised flag. -/
theorem convert32To64_exact (mode : RoundingMode) (w : fp32.Word) (q : ℚ)
    (h : (Datum.decode fp32 w).toRat? = some q) :
    fp64.decode? (convert fp32 fp64 mode w).value = some (q : ℝ) ∧
      (convert fp32 fp64 mode w).flags = Flags.empty := by
  have hs := rat_representable_of_decode fp32 w q h
  have hd : binary64.Representable (q : ℝ) := representable_mono binary32 binary64 (q : ℝ)
    (by norm_num [binary32, binary64]) (by norm_num [binary32, binary64])
    (by norm_num [binary32, binary64, Format.precision]) hs
  have hq : |q| < (2 : ℚ)^(128 : ℤ) := by
    have hr := representable_abs_lt_next binary32 (q : ℝ) hs
    change |(q : ℝ)| < (2 : ℝ)^(128 : ℤ) at hr
    exact_mod_cast hr
  have ho := noOverflow_of_abs_lt_pow binary64 mode q 128 hq (by decide +kernel)
  change overflowWithMode fp64.format mode q = false at ho
  have hex := scaledRound_exact fp64.format mode q hd
  rw [convert_finite fp32 fp64 mode w q h]
  constructor
  · have hv := roundWithMode_projection fp64 mode q (Datum.decode fp32 w).fields.negative ho
    rw [hex] at hv
    rw [← Datum.toRat?_decode, hv]
    rfl
  · funext e
    cases e <;> simp [roundWithMode, roundingFlags, ho, hex, Flags.empty]

end FP.IEEE.Software
