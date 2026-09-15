import FP.IEEE.Software.ScaledRound

/-! Exact encoding of representable rational values. Normalization uses integer
shifts; the reference encoder searches only the finite exponent range, never
the space of bit patterns. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

/-- Move a short significand toward the minimum exponent until it is normal.
The second component is an offset from the least subnormal exponent. -/
def normalizeCoeff (f : ℕ) (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (m, 0)
  | k + 1 => if m < 2 ^ f then normalizeCoeff f (2 * m) k else (m, k + 1)

theorem normalizeCoeff_spec (f m k : ℕ) (hm : m < 2 ^ (f + 1)) :
    (normalizeCoeff f m k).1 < 2 ^ (f + 1) ∧
    (normalizeCoeff f m k).2 ≤ k ∧
    (2 ^ f ≤ (normalizeCoeff f m k).1 ∨ (normalizeCoeff f m k).2 = 0) ∧
    (normalizeCoeff f m k).1 * 2 ^ (normalizeCoeff f m k).2 = m * 2 ^ k := by
  induction k generalizing m with
  | zero => exact ⟨hm, le_rfl, Or.inr rfl, rfl⟩
  | succ k ih =>
    simp only [normalizeCoeff]
    split_ifs with hshort
    · have hdouble : 2 * m < 2 ^ (f + 1) := by rw [pow_succ]; omega
      obtain ⟨hb, hk, hn, hv⟩ := ih (2 * m) hdouble
      refine ⟨hb, hk.trans (by omega), hn, ?_⟩
      rw [hv, pow_succ]; ring
    · exact ⟨hm, le_rfl, Or.inl (by omega), rfl⟩

/-- Exponent offset encoded as a biased exponent; offset zero is the
subnormal binade and normal significands at that offset use exponent one. -/
def coefficientFields (I : Interchange) (negative : Bool) (m k : ℕ) : Fields I :=
  ⟨negative, BitVec.ofNat I.exponentBits (if m < 2 ^ I.format.fractionBits then 0 else k + 1),
    BitVec.ofNat I.format.fractionBits (m % 2 ^ I.format.fractionBits)⟩

theorem coefficientFields_spec (I : Interchange) [I.Valid] (negative : Bool) (m k : ℕ)
    (hm : m < 2 ^ (I.format.fractionBits + 1))
    (hk : k ≤ 2 ^ I.exponentBits - 3)
    (hn : 2 ^ I.format.fractionBits ≤ m ∨ k = 0)
    (he : 3 ≤ 2 ^ I.exponentBits) :
    I.IsFinite (coefficientFields I negative m k).pack ∧
    (coefficientFields I negative m k).rationalValue =
      (if negative then -1 else 1) * (m : ℚ) *
        (2 : ℚ) ^ (I.format.emin - I.format.fractionBits + (k : ℤ)) := by
  have hp : 0 < 2 ^ I.format.fractionBits := by positivity
  have hb : k + 1 < 2 ^ I.exponentBits := by omega
  have hx : (coefficientFields I negative m k).exponent.toNat =
      if m < 2 ^ I.format.fractionBits then 0 else k + 1 := by
    simp only [coefficientFields, BitVec.toNat_ofNat]
    split_ifs <;> simp [Nat.mod_eq_of_lt, hb]
  have hf : (coefficientFields I negative m k).fraction.toNat = m % 2 ^ I.format.fractionBits := by
    simp [coefficientFields]
  have hz : (coefficientFields I negative m k).exponent = 0 ↔ m < 2 ^ I.format.fractionBits := by
    rw [← BitVec.toNat_inj, hx]
    split_ifs <;> simp_all
  constructor
  · rw [Fields.isFinite_pack, Ne, ← BitVec.toNat_inj, hx, BitVec.toNat_allOnes]
    split_ifs <;> omega
  · simp only [Fields.rationalValue, hz, hx, hf]
    change (if negative then -1 else 1) * _ * _ = _
    by_cases hs : m < 2 ^ I.format.fractionBits
    all_goals simp only [hs, if_true, if_false]
    · have hk0 : k = 0 := by omega
      rw [Nat.mod_eq_of_lt hs, hk0]
      simp
    · have hmod : m % 2 ^ I.format.fractionBits = m - 2 ^ I.format.fractionBits := by
        rw [pow_succ] at hm
        have hdiv : m / 2 ^ I.format.fractionBits = 1 := by
          apply Nat.div_eq_of_lt_le <;> omega
        have hr := Nat.mod_add_div m (2 ^ I.format.fractionBits)
        rw [hdiv] at hr
        omega
      have hmadd : 2 ^ I.format.fractionBits + m % 2 ^ I.format.fractionBits = m := by omega
      rw [hmadd]
      congr 2
      rw [I.emin_eq]
      push_cast
      ring

theorem exponent_space (I : Interchange) : 3 ≤ 2 ^ I.exponentBits := by
  have h := I.format.exponent_order
  rw [I.emin_eq, I.emax_eq] at h
  have hh : (3 : ℤ) ≤ 2 ^ I.exponentBits := by omega
  exact_mod_cast hh

def maxOffset (I : Interchange) : ℕ := 2 ^ I.exponentBits - 3

theorem maxOffset_eq (I : Interchange) :
    (maxOffset I : ℤ) = I.format.emax - I.format.emin := by
  unfold maxOffset
  rw [Nat.cast_sub (exponent_space I)]
  rw [I.emax_eq, I.emin_eq]
  push_cast
  ring

def coefficient (I : Interchange) (q : ℚ) (k : ℕ) : ℕ :=
  ⌊|q| / (2 : ℚ) ^ (I.format.emin - I.format.fractionBits + (k : ℤ))⌋₊

def CoefficientValid (I : Interchange) (q : ℚ) (k : ℕ) : Prop :=
  (coefficient I q k : ℚ) * (2 : ℚ) ^ (I.format.emin - I.format.fractionBits + (k : ℤ)) = |q| ∧
    coefficient I q k < 2 ^ (I.format.fractionBits + 1)

instance (I : Interchange) (q : ℚ) (k : ℕ) : Decidable (CoefficientValid I q k) :=
  inferInstanceAs (Decidable (_ ∧ _))

def findCoefficient (I : Interchange) (q : ℚ) : Option ℕ :=
  (List.range (maxOffset I + 1)).find? (fun k => decide (CoefficientValid I q k))

/-- Preserve an explicitly supplied zero sign; nonzero signs follow the value. -/
def valueSign (q : ℚ) (zeroSign : Bool) : Bool :=
  if q = 0 then zeroSign else decide (q < 0)

theorem valueSign_abs (q : ℚ) (zeroSign : Bool) :
    (if valueSign q zeroSign then (-1 : ℚ) else 1) * |q| = q := by
  by_cases hz : q = 0
  · subst q; simp
  · by_cases hn : q < 0
    · simp [valueSign, hz, hn, abs_of_neg hn]
    · simp [valueSign, hz, hn, abs_of_nonneg (le_of_not_gt hn)]

def encodeFinite? (I : Interchange) (q : ℚ) (zeroSign : Bool := false) : Option I.Word := do
  let k ← findCoefficient I q
  let c := normalizeCoeff I.format.fractionBits (coefficient I q k) k
  some (coefficientFields I (valueSign q zeroSign) c.1 c.2).pack

theorem findCoefficient_valid (I : Interchange) (q : ℚ) (k : ℕ)
    (h : findCoefficient I q = some k) : k ≤ maxOffset I ∧ CoefficientValid I q k := by
  have hm := List.mem_of_find?_eq_some h
  have hv := List.find?_some h
  exact ⟨by simpa only [List.mem_range, Nat.lt_succ_iff] using hm,
    by simpa using hv⟩

theorem encodeFinite?_sound (I : Interchange) [I.Valid] (q : ℚ) (zeroSign : Bool)
    (w : I.Word) (h : encodeFinite? I q zeroSign = some w) :
    I.decode? w = some (q : ℝ) ∧ I.negative w = valueSign q zeroSign := by
  cases hk : findCoefficient I q with
  | none => simp [encodeFinite?, hk] at h
  | some k =>
    obtain ⟨hb, hv, hm⟩ := findCoefficient_valid I q k hk
    obtain ⟨hc, hck, hcn, hcv⟩ := normalizeCoeff_spec I.format.fractionBits (coefficient I q k) k hm
    let c := normalizeCoeff I.format.fractionBits (coefficient I q k) k
    have heq : w = (coefficientFields I (valueSign q zeroSign) c.1 c.2).pack := by
      simpa [encodeFinite?, hk, c] using h.symm
    rw [heq]
    obtain ⟨hf, hval⟩ := coefficientFields_spec I (valueSign q zeroSign) c.1 c.2
      hc (hck.trans hb) hcn (exponent_space I)
    have hvq : (coefficientFields I (valueSign q zeroSign) c.1 c.2).rationalValue = q := by
      rw [hval]
      have hcq : (c.1 : ℚ) * (2 : ℚ) ^ c.2 = (coefficient I q k : ℚ) * (2 : ℚ)^k := by
        exact_mod_cast hcv
      have hscale : (c.1 : ℚ) * (2 : ℚ) ^ (I.format.emin - I.format.fractionBits + (c.2 : ℤ)) = |q| := by
        rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
        calc
          _ = ((c.1 : ℚ) * (2 : ℚ)^c.2) * (2 : ℚ)^(I.format.emin - I.format.fractionBits) := by ring
          _ = ((coefficient I q k : ℚ) * (2 : ℚ)^k) * (2 : ℚ)^(I.format.emin - I.format.fractionBits) := by rw [hcq]
          _ = |q| := by rw [← hv, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]; ring
      rw [mul_assoc, hscale, valueSign_abs]
    constructor
    · rw [I.decode?_eq _ hf, ← Fields.rationalValue_cast, hvq]
    · simp [coefficientFields]

/-- Every value in the independently defined real representable set is encodable. -/
theorem findCoefficient_complete (I : Interchange) (q : ℚ)
    (hq : I.format.Representable (q : ℝ)) : (findCoefficient I q).isSome = true := by
  obtain ⟨m, e, hel, heu, hm, hv⟩ := hq
  let k := (e - (I.format.emin - I.format.fractionBits)).toNat
  have hk : (k : ℤ) = e - (I.format.emin - I.format.fractionBits) :=
    Int.toNat_of_nonneg (by omega)
  have hke : I.format.emin - I.format.fractionBits + (k : ℤ) = e := by omega
  have hkb : k ≤ maxOffset I := by
    have hb := maxOffset_eq I
    omega
  have hqval : q = (m : ℚ) * (2 : ℚ)^e := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hv
  have habs : |q| = (m.natAbs : ℚ) * (2 : ℚ)^e := by
    rw [hqval, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2^e)]
    simp
  have hcoeff : coefficient I q k = m.natAbs := by
    unfold coefficient
    rw [hke, habs, mul_div_cancel_right₀ _ (by positivity : (2 : ℚ)^e ≠ 0)]
    exact Nat.floor_natCast _
  apply List.find?_isSome.mpr
  refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
  simp only [decide_eq_true_eq, CoefficientValid, hcoeff, hke]
  refine ⟨habs.symm, ?_⟩
  have hm' : (m.natAbs : ℝ) < (2 : ℝ) ^ (I.format.fractionBits + 1) := by
    simpa [Format.precision] using hm
  exact_mod_cast hm'

theorem encodeFinite?_complete (I : Interchange) (q : ℚ) (zeroSign : Bool)
    (hq : I.format.Representable (q : ℝ)) : (encodeFinite? I q zeroSign).isSome = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (findCoefficient_complete I q hq)
  simp [encodeFinite?, hk]

/-- Total exact encoder on representable values; its proof argument is erased. -/
def encodeFinite (I : Interchange) (q : ℚ) (zeroSign : Bool)
    (hq : I.format.Representable (q : ℝ)) : I.Word :=
  (encodeFinite? I q zeroSign).get (encodeFinite?_complete I q zeroSign hq)

theorem encodeFinite_spec (I : Interchange) [I.Valid] (q : ℚ) (zeroSign : Bool)
    (hq : I.format.Representable (q : ℝ)) :
    I.decode? (encodeFinite I q zeroSign hq) = some (q : ℝ) ∧
      I.negative (encodeFinite I q zeroSign hq) = valueSign q zeroSign := by
  apply encodeFinite?_sound
  exact (Option.some_get _).symm

end FP.IEEE.Software
