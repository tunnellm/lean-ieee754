import FP.IEEE.Software.IntegerRound
import FP.IEEE.Projection

/-! Executable binary grid selection and scaled rational rounding. The nearest-
even specialization refines the existing finite-value specification exactly.
This module does not yet encode rounded results or claim exception-flag correctness. -/
namespace FP.IEEE.Software

def quantumExponent (F : Format) (x : ℚ) : ℤ :=
  max F.emin (Int.log 2 |x|) - F.fractionBits

def quantum (F : Format) (x : ℚ) : ℚ := (2 : ℚ) ^ quantumExponent F x

def scaledRound (F : Format) (mode : RoundingMode) (x : ℚ) : ℚ :=
  (roundInt mode (x / quantum F x) : ℚ) * quantum F x

def overflowThreshold (F : Format) : ℚ :=
  ((2 : ℚ) ^ (F.fractionBits + 1) - 1 / 2) *
    (2 : ℚ) ^ (F.emax - F.fractionBits)

/-- Finite nearest-even projection, with exactly the existing overflow boundary. -/
def roundNearest? (F : Format) (x : ℚ) : Option ℚ :=
  if |x| < overflowThreshold F then some (scaledRound F .nearestEven x) else none

theorem log_abs_cast (x : ℚ) : Int.log 2 |(x : ℝ)| = Int.log 2 |x| := by
  by_cases hx : x = 0
  · subst x; simp
  have hp : 0 < |x| := abs_pos.mpr hx
  have hpR : (0 : ℝ) < |(x : ℝ)| := by exact_mod_cast hp
  have hlo : (2 : ℝ) ^ Int.log 2 |x| ≤ |(x : ℝ)| := by
    have h := Rat.cast_le (K := ℝ) |>.mpr
      (Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) hp)
    simpa only [Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_ofNat, Rat.cast_abs] using h
  have hhi : |(x : ℝ)| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
    have h := Rat.cast_lt (K := ℝ) |>.mpr
      (Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) |x|)
    simpa only [Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_ofNat, Rat.cast_abs] using h
  have ha := (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hpR).mp hlo
  have hb := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hpR).mp hhi
  omega

@[simp] theorem quantumExponent_cast (F : Format) (x : ℚ) :
    F.quantumExponent (x : ℝ) = quantumExponent F x := by
  simp [Format.quantumExponent, quantumExponent, log_abs_cast]

@[simp] theorem quantum_cast (F : Format) (x : ℚ) :
    (quantum F x : ℝ) = F.quantum (x : ℝ) := by
  simp [quantum, Format.quantum]

theorem quantum_pos (F : Format) (x : ℚ) : 0 < quantum F x := by
  unfold quantum; positivity

/-- This is a refinement theorem between executable rational arithmetic and
our independently defined real nearest-even specification. -/
theorem scaledRound_even_cast (F : Format) (x : ℚ) :
    (scaledRound F .nearestEven x : ℝ) = F.roundFinite (x : ℝ) := by
  unfold scaledRound Format.roundFinite
  push_cast
  rw [roundInt_even_equiv]
  simp

@[simp] theorem overflowThreshold_cast (F : Format) :
    (overflowThreshold F : ℝ) = F.overflowThreshold := by
  simp [overflowThreshold, Format.overflowThreshold]

theorem roundNearest?_cast (F : Format) (x : ℚ) :
    (roundNearest? F x).map (fun q : ℚ => (q : ℝ)) = F.round? (x : ℝ) := by
  have hc : |(x : ℝ)| < F.overflowThreshold ↔ |x| < overflowThreshold F := by
    rw [← overflowThreshold_cast]
    simpa only [Rat.cast_abs] using
      (Rat.cast_lt (K := ℝ) (p := |x|) (q := overflowThreshold F))
  simp only [roundNearest?, Format.round?, hc]
  split <;> simp [scaledRound_even_cast]

theorem scaledRound_nearest_error (F : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : ℚ) :
    |scaledRound F mode x - x| ≤ quantum F x / 2 := by
  have hp := quantum_pos F x
  have he := mul_le_mul_of_nonneg_right
    (roundInt_nearest_error mode hm (x / quantum F x)) hp.le
  have hi : |scaledRound F mode x - x| =
      |(roundInt mode (x / quantum F x) : ℚ) - x / quantum F x| * quantum F x := by
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp]
    unfold scaledRound
    congr 1
    field_simp
  rw [hi]
  linarith

theorem scaledRound_nearest (F : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : ℚ) (k : ℤ) :
    |scaledRound F mode x - x| ≤ |(k : ℚ) * quantum F x - x| := by
  have hp := quantum_pos F x
  have he := mul_le_mul_of_nonneg_right
    (roundInt_nearest mode hm (x / quantum F x) k) hp.le
  have hi : ∀ a : ℚ, |a - x / quantum F x| * quantum F x = |a * quantum F x - x| := by
    intro a
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp]
    congr 1
    field_simp
  simpa only [hi, scaledRound] using he

/-- Existing representability results transfer to the executable specialization. -/
theorem roundNearest?_representable (F : Format) (x y : ℚ)
    (h : roundNearest? F x = some y) : F.Representable (y : ℝ) := by
  have hr := roundNearest?_cast F x
  rw [h] at hr
  simp only [Option.map_some] at hr
  unfold Format.round? at hr
  split_ifs at hr with hs
  · have hy : (y : ℝ) = F.roundFinite (x : ℝ) := Option.some.inj hr
    rw [hy]
    exact F.roundFinite_representable hs

end FP.IEEE.Software
