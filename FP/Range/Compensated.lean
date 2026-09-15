import FP.Range.Interval
import FP.CompensationInput

/-! Input-domain certificates for compensated sums and online Dot2.
All executable quantities are rational; `none` means insufficient certification. -/
namespace FP.Range

def Interval.symmetric (e : ℚ) : Interval := ⟨-e, e⟩
def Interval.singleton (x : ℚ) : Interval := ⟨x, x⟩

theorem Interval.contains_symmetric {e : ℚ} {x : ℝ} (h : |x| ≤ (e : ℝ)) :
    (Interval.symmetric e).Contains x := by
  simpa [Interval.Contains, Interval.symmetric] using abs_le.mp h

theorem Interval.contains_singleton (x : ℚ) : (Interval.singleton x).Contains (x : ℝ) :=
  ⟨le_rfl, le_rfl⟩

def roundErrorBound (p : Params) (J : Interval) : ℚ := p.u * J.radius + p.ε

theorem roundErrorBound_sound (F : IEEE.Format) {J : Interval} {x : ℝ}
    (hx : J.Contains x) :
    |F.roundFinite x - x| ≤ (roundErrorBound (.ofFormat F) J : ℝ) := by
  have he := F.roundFinite_mixed_error x
  have hm := mul_le_mul_of_nonneg_left (Interval.abs_le_radius hx) F.unitRoundoff_pos.le
  simp only [roundErrorBound, Rat.cast_add, Rat.cast_mul, Params.ofFormat_u, Params.ofFormat_ε]
  linarith

theorem interval_range (F : IEEE.Format) {J : Interval} {x : ℝ}
    (hx : J.Contains x) (h : J.radius < (Params.ofFormat F).threshold) :
    |x| < F.overflowThreshold := by
  have hr : (J.radius : ℝ) < ((Params.ofFormat F).threshold : ℝ) := by exact_mod_cast h
  exact (Interval.abs_le_radius hx).trans_lt (by simpa using hr)

/-- The two components enclose the rounded high value and the exact residual. -/
def checkTwoSum (p : Params) (S A : Interval) : Option (Interval × Interval) := do
  if S.Valid ∧ A.Valid then
    let H ← checkRound p (S.add A)
    let e := roundErrorBound p (S.add A)
    if (A.inflate e).radius < p.threshold then
      some (H, .symmetric e)
    else none
  else none

/-- The low component allows a half-subnormal product decomposition defect. -/
def checkTwoProduct (p : Params) (A B : Interval) : Option (Interval × Interval) := do
  if A.Valid ∧ B.Valid then
    let H ← checkRound p (A.mul B)
    some (H, .symmetric (roundErrorBound p (A.mul B) + p.ε))
  else none

structure CompensatedState where
  high : Interval
  correction : Interval
  deriving Repr, DecidableEq

def CompensatedState.zero : CompensatedState := ⟨.zero, .zero⟩

def checkCompensatedStep (p : Params) (s : CompensatedState) (A : Interval) :
    Option CompensatedState := do
  if s.correction.Valid then
    let h ← checkTwoSum p s.high A
    let c ← checkRound p (s.correction.add h.2)
    some ⟨h.1, c⟩
  else none

def checkCompensatedPass (p : Params) (s : CompensatedState) : List Interval → Option CompensatedState
  | [] => if s.high.Valid ∧ s.correction.Valid then some s else none
  | a :: xs => do
    let t ← checkCompensatedStep p s a
    checkCompensatedPass p t xs

def checkCompensatedDotStep (p : Params) (s : CompensatedState) (A B : Interval) :
    Option CompensatedState := do
  if s.correction.Valid then
    let prod ← checkTwoProduct p A B
    let h ← checkTwoSum p s.high prod.1
    let t ← checkRound p (prod.2.add h.2)
    let c ← checkRound p (s.correction.add t)
    some ⟨h.1, c⟩
  else none

def checkCompensatedDotPass (p : Params) (A B : ℕ → Interval) : ℕ → Option CompensatedState
  | 0 => some .zero
  | n+1 => do
    let s ← checkCompensatedDotPass p A B n
    checkCompensatedDotStep p s (A n) (B n)

def checkCompensatedFinish (p : Params) (s : CompensatedState) : Option Interval :=
  if s.high.Valid ∧ s.correction.Valid then checkRound p (s.high.add s.correction) else none

def exactSumInterval : List Interval → Interval
  | [] => .zero
  | a :: xs => a.add (exactSumInterval xs)

def sumIntervalMass (xs : List Interval) : ℚ := (xs.map Interval.radius).sum

def exactDotInterval (A B : ℕ → Interval) : ℕ → Interval
  | 0 => .zero
  | n+1 => (exactDotInterval A B n).add ((A n).mul (B n))

def dotIntervalMass (A B : ℕ → Interval) : ℕ → ℚ
  | 0 => 0
  | n+1 => dotIntervalMass A B n + ((A n).mul (B n)).radius

def growthRat (u : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => (1+u)*growthRat u n+u

def geomWeightRat (u : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => 1+(1+u)*geomWeightRat u n

@[simp] theorem growthRat_cast (u : ℚ) (n : ℕ) : (growthRat u n : ℝ) = growth (u : ℝ) n := by
  induction n with
  | zero => simp [growthRat, growth]
  | succ n ih => simp [growthRat, ih, growth, pow_succ]; ring

@[simp] theorem geomWeightRat_cast (u : ℚ) (n : ℕ) :
    (geomWeightRat u n : ℝ) = geomWeight (u : ℝ) n := by
  induction n with
  | zero => simp [geomWeightRat]
  | succ n ih => simp [geomWeightRat, ih, geomWeight_succ]

def sumAccuracyBound (p : Params) (T : Interval) (M : ℚ) (n : ℕ) : ℚ :=
  p.u*T.radius+(1+p.u)*((growthRat p.u n)^2*M+
    p.ε*(1+growthRat p.u n)*geomWeightRat p.u n)+p.ε

def dotAccuracyBound (p : Params) (T : Interval) (M : ℚ) (n : ℕ) : ℚ :=
  p.u*T.radius+(1+p.u)*((growthRat p.u (2*n))^2*M+
    p.ε*(1+growthRat p.u (2*n))*(geomWeightRat p.u (2*n)+n))+p.ε

/-- Soundness is conditional on checker success and finite input containment. -/
structure AccuracyCertificate where
  resultInterval : Interval
  exactInterval : Interval
  errorBound : ℚ
  deriving Repr, DecidableEq

def AccuracyCertificate.zero : AccuracyCertificate := ⟨.zero, .zero, 0⟩

def checkCompensatedSum (p : Params) (bounds : List Interval) : Option AccuracyCertificate :=
  if bounds = [] then some .zero else do
    let s ← checkCompensatedPass p .zero bounds
    let r ← checkCompensatedFinish p s
    let T := exactSumInterval bounds
    some ⟨r, T, sumAccuracyBound p T (sumIntervalMass bounds) bounds.length⟩

def checkCompensatedDot (p : Params) (A B : ℕ → Interval) (n : ℕ) : Option AccuracyCertificate :=
  if n = 0 then some .zero else do
    let s ← checkCompensatedDotPass p A B n
    let r ← checkCompensatedFinish p s
    let T := exactDotInterval A B n
    some ⟨r, T, dotAccuracyBound p T (dotIntervalMass A B n) n⟩

def checkCompensatedDotList (p : Params) (bounds : List (Interval × Interval)) :
    Option AccuracyCertificate :=
  checkCompensatedDot p (fun i => (bounds[i]?.getD (.zero,.zero)).1)
    (fun i => (bounds[i]?.getD (.zero,.zero)).2) bounds.length

end FP.Range
