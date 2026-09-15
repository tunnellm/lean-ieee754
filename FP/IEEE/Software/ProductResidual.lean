import FP.IEEE.Software.FMA
import FP.IEEE.Software.Sign
import FP.IEEE.Software.Exactness

/-! FMA-based product residuals with a checked error-free decomposition certificate.
The rounded product may be inexact. Only the residual must be computed exactly. -/
set_option backward.isDefEq.respectTransparency false
namespace FP.IEEE.Software
open Interchange

theorem negate_toRat? (I : Interchange) [I.Valid] (a : I.Word) :
    (Datum.decode I (negate I a).value).toRat? =
      (Datum.decode I a).toRat?.map (fun q => -q) := by
  have he : (negate I a).value =
      ((Datum.decode I a).withSign (!(Datum.decode I a).fields.negative)).encode := by
    simp [negate, Result.pure, Datum.encode, Datum.decode]
  rw [he, Datum.decode_encode]
  generalize Datum.decode I a = d
  cases d <;> simp [Datum.withSign, Datum.toRat?, Datum.isFinite, Datum.fields, Fields.rationalValue]
  all_goals split_ifs <;> simp_all <;> ring

def productResidual (I : Interchange) [I.Valid] (a b : I.Word) : Result I.Word :=
  fma I .nearestEven a b (negate I (mul I .nearestEven a b).value).value

def twoProduct (I : Interchange) [I.Valid] (a b : I.Word) : Result (I.Word × I.Word) :=
  let p := mul I .nearestEven a b
  let e := productResidual I a b
  ⟨(p.value,e.value), Flags.union p.flags e.flags⟩

/-- Reject a nonfinite high part or an inexact/exceptional residual. Retain sticky flags
from the high multiplication, whose inexact flag is compatible with an exact decomposition. -/
def certifiedTwoProduct? (I : Interchange) [I.Valid] (a b : I.Word) : Option (Result (I.Word × I.Word)) := do
  let _ ← (Datum.decode I (mul I .nearestEven a b).value).toRat?
  if flagsClear (productResidual I a b).flags then some (twoProduct I a b) else none

theorem productResidual_finite (I : Interchange) [I.Valid] (a b : I.Word) (x y p : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hp : (Datum.decode I (mul I .nearestEven a b).value).toRat? = some p) :
    productResidual I a b = roundWithMode I .nearestEven (x*y-p)
      (Spec.fmaZeroSign .nearestEven (Datum.decode I a) (Datum.decode I b)
        (Datum.decode I (negate I (mul I .nearestEven a b).value).value)) := by
  unfold productResidual fma
  have hn : (Datum.decode I (negate I (mul I .nearestEven a b).value).value).toRat? = some (-p) := by
    rw [negate_toRat?, hp]; rfl
  simpa [sub_eq_add_neg] using mixedFma_finite I I I I .nearestEven a b _ x y (-p) ha hb hn

/-- A successful certificate gives an exact real decomposition of the product. -/
theorem certifiedTwoProduct?_sound (I : Interchange) [I.Valid] (a b : I.Word) (x y : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (r : Result (I.Word × I.Word)) (hr : certifiedTwoProduct? I a b = some r) :
    ∃ p e : ℝ, I.decode? r.value.1 = some p ∧ I.decode? r.value.2 = some e ∧ (x : ℝ)*(y : ℝ) = p+e := by
  unfold certifiedTwoProduct? at hr
  cases hp : (Datum.decode I (mul I .nearestEven a b).value).toRat? with
  | none => simp [hp] at hr
  | some p =>
    simp only [hp] at hr
    change (if flagsClear (productResidual I a b).flags then some (twoProduct I a b) else none) = some r at hr
    split_ifs at hr with hf
    cases Option.some.inj hr
    have he := flagsClear_iff _ |>.mp hf
    have heq := productResidual_finite I a b x y p ha hb hp
    rw [heq] at he
    have hd := roundWithMode_exact_of_no_flags I .nearestEven (x*y-p) _ he
    rw [← heq] at hd
    refine ⟨(p : ℝ), ((x*y-p : ℚ) : ℝ), ?_, hd, ?_⟩
    · change I.decode? (mul I .nearestEven a b).value = _
      rw [← Datum.toRat?_decode, hp]; rfl
    · push_cast; ring

/-- The certificate succeeds whenever the exact residual is representable.
This is an explicit range qualification, not an assumed rounding-error property. -/
theorem certifiedTwoProduct?_complete (I : Interchange) [I.Valid] (a b : I.Word) (x y p : ℚ)
    (ha : (Datum.decode I a).toRat? = some x) (hb : (Datum.decode I b).toRat? = some y)
    (hp : (Datum.decode I (mul I .nearestEven a b).value).toRat? = some p)
    (he : I.format.Representable ((x*y-p : ℚ) : ℝ)) :
    certifiedTwoProduct? I a b = some (twoProduct I a b) := by
  have hf : (productResidual I a b).flags = Flags.empty := by
    rw [productResidual_finite I a b x y p ha hb hp]
    exact (roundWithMode_exact I .nearestEven _ _ he).2
  simp [certifiedTwoProduct?, hp, (flagsClear_iff _).mpr hf]
end FP.IEEE.Software
