import FP.IEEE.Projection
import FP.IEEE.Environment

/-! Executable quiet sign operations on raw encodings. They never canonicalize
NaNs or raise invalid, including for signaling NaN inputs. -/
namespace FP.IEEE.Software
open Interchange

def copy (I : Interchange) (w : I.Word) : Result I.Word := Result.pure w

def copySign (I : Interchange) (w sign : I.Word) : Result I.Word :=
  Result.pure (((Fields.unpack I w).withSign (I.negative sign)).pack)

def negate (I : Interchange) (w : I.Word) : Result I.Word :=
  Result.pure (((Fields.unpack I w).withSign (!I.negative w)).pack)

def abs (I : Interchange) (w : I.Word) : Result I.Word :=
  Result.pure (((Fields.unpack I w).withSign false).pack)

@[simp] theorem copySign_fields (I : Interchange) (w sign : I.Word) :
    Fields.unpack I (copySign I w sign).value =
      (Fields.unpack I w).withSign (I.negative sign) := by
  simp [copySign, Result.pure]
@[simp] theorem negate_fields (I : Interchange) (w : I.Word) :
    Fields.unpack I (negate I w).value =
      (Fields.unpack I w).withSign (!I.negative w) := by
  simp [negate, Result.pure]
@[simp] theorem abs_fields (I : Interchange) (w : I.Word) :
    Fields.unpack I (abs I w).value = (Fields.unpack I w).withSign false := by
  simp [abs, Result.pure]

@[simp] theorem negate_sign (I : Interchange) (w : I.Word) :
    I.negative (negate I w).value = !I.negative w := by
  simp [negate, Result.pure, Fields.withSign]
@[simp] theorem abs_sign (I : Interchange) (w : I.Word) :
    I.negative (abs I w).value = false := by
  simp [abs, Result.pure, Fields.withSign]

@[simp] theorem negate_negate (I : Interchange) (w : I.Word) :
    (negate I (negate I w).value).value = w := by
  simp only [negate, Result.pure, Fields.unpack_pack, Fields.negative_pack]
  change ((Fields.unpack I w).withSign (!(!I.negative w))).pack = w
  simp only [Bool.not_not]
  have h : (Fields.unpack I w).withSign (I.negative w) = Fields.unpack I w := rfl
  rw [h, Fields.pack_unpack]

@[simp] theorem abs_abs (I : Interchange) (w : I.Word) :
    (abs I (abs I w).value).value = (abs I w).value := by
  simp [abs, Result.pure]

/-- These are whole-field equalities, including every NaN payload bit. -/
theorem sign_operations_preserve_fraction (I : Interchange) (w sign : I.Word) :
    I.fraction (negate I w).value = I.fraction w ∧
    I.fraction (abs I w).value = I.fraction w ∧
    I.fraction (copySign I w sign).value = I.fraction w := by
  simp [negate, abs, copySign, Result.pure, Fields.withSign]

theorem sign_operations_preserve_exponent (I : Interchange) (w sign : I.Word) :
    I.exponent (negate I w).value = I.exponent w ∧
    I.exponent (abs I w).value = I.exponent w ∧
    I.exponent (copySign I w sign).value = I.exponent w := by
  simp [negate, abs, copySign, Result.pure, Fields.withSign]

theorem sign_operations_quiet (I : Interchange) (w sign : I.Word) :
    (copy I w).flags = Flags.empty ∧ (negate I w).flags = Flags.empty ∧
    (abs I w).flags = Flags.empty ∧ (copySign I w sign).flags = Flags.empty := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end FP.IEEE.Software
