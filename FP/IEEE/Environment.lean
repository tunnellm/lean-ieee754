import FP.Basic

/-! Explicit default-handling state. Flags are sticky, operation-local flags
are distinguished from saved state, and no host floating-point environment is used. -/
namespace FP.IEEE

inductive RoundingMode where
  | nearestEven | nearestAway | towardZero | towardPositive | towardNegative
  deriving DecidableEq, Repr, Inhabited

/-- Rounding direction for the magnitude of a negative operand. -/
def RoundingMode.reverse : RoundingMode → RoundingMode
  | .towardPositive => .towardNegative
  | .towardNegative => .towardPositive
  | m => m

@[simp] theorem RoundingMode.reverse_reverse (m : RoundingMode) :
    m.reverse.reverse = m := by cases m <;> rfl

inductive Exception where
  | invalid | divideByZero | overflow | underflow | inexact
  deriving DecidableEq, Repr, Inhabited

abbrev Flags := Exception → Bool

namespace Flags

def empty : Flags := fun _ => false

def singleton (e : Exception) : Flags := fun f => decide (f = e)

def union (a b : Flags) : Flags := fun e => a e || b e

def lower (a mask : Flags) : Flags := fun e => a e && !mask e

/-- Restore only selected flags, leaving all other flags unchanged. -/
def restore (current saved mask : Flags) : Flags :=
  fun e => if mask e then saved e else current e

def test (a mask : Flags) : Bool :=
  [Exception.invalid, .divideByZero, .overflow, .underflow, .inexact].any
    (fun e => a e && mask e)

def LE (a b : Flags) : Prop := ∀ e, a e = true → b e = true

@[simp] theorem union_empty (a : Flags) : union a empty = a := by
  funext e; simp [union, empty]
@[simp] theorem empty_union (a : Flags) : union empty a = a := by
  funext e; simp [union, empty]
@[simp] theorem union_self (a : Flags) : union a a = a := by
  funext e; simp [union]
theorem union_assoc (a b c : Flags) : union (union a b) c = union a (union b c) := by
  funext e; simp [union, Bool.or_assoc]
theorem union_comm (a b : Flags) : union a b = union b a := by
  funext e; simp [union, Bool.or_comm]
theorem le_union_left (a b : Flags) : LE a (union a b) := by
  intro e he; simp [union, he]
theorem le_union_right (a b : Flags) : LE b (union a b) := by
  intro e he; simp [union, he]
@[simp] theorem lower_selected (a mask : Flags) (e : Exception) (h : mask e = true) :
    lower a mask e = false := by simp [lower, h]
@[simp] theorem lower_unselected (a mask : Flags) (e : Exception) (h : mask e = false) :
    lower a mask e = a e := by simp [lower, h]
@[simp] theorem restore_selected (a saved mask : Flags) (e : Exception)
    (h : mask e = true) : restore a saved mask e = saved e := by simp [restore, h]
@[simp] theorem restore_unselected (a saved mask : Flags) (e : Exception)
    (h : mask e = false) : restore a saved mask e = a e := by simp [restore, h]
@[simp] theorem restore_self (a mask : Flags) : restore a a mask = a := by
  funext e; simp [restore]

theorem test_iff (a mask : Flags) :
    test a mask = true ↔ ∃ e, a e = true ∧ mask e = true := by
  simp only [test, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨e, _, h⟩; exact ⟨e, h⟩
  · rintro ⟨e, h⟩
    exact ⟨e, by cases e <;> simp, h⟩
end Flags

/-- An operation's result and newly raised flags, before sticky accumulation. -/
structure Result (α : Type) where
  value : α
  flags : Flags := Flags.empty

namespace Result

def pure (a : α) : Result α := ⟨a, Flags.empty⟩
def bind (r : Result α) (f : α → Result β) : Result β :=
  let s := f r.value
  ⟨s.value, Flags.union r.flags s.flags⟩

@[simp] theorem pure_bind (a : α) (f : α → Result β) : (pure a).bind f = f a := by
  simp [pure, bind]
@[simp] theorem bind_pure (r : Result α) : r.bind pure = r := by
  cases r; simp [bind, pure]
theorem bind_assoc (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (r.bind f).bind g = r.bind (fun a => (f a).bind g) := by
  simp [bind, Flags.union_assoc]

theorem flags_sticky (r : Result α) (f : α → Result β) :
    Flags.LE r.flags (r.bind f).flags := Flags.le_union_left _ _
end Result

structure Env where
  mode : RoundingMode := .nearestEven
  flags : Flags := Flags.empty

namespace Env

def setMode (env : Env) (mode : RoundingMode) : Env := { env with mode := mode }
def raiseFlags (env : Env) (mask : Flags) : Env :=
  { env with flags := Flags.union env.flags mask }
def lowerFlags (env : Env) (mask : Flags) : Env :=
  { env with flags := Flags.lower env.flags mask }
def saveAllFlags (env : Env) : Flags := env.flags
def restoreFlags (env : Env) (saved mask : Flags) : Env :=
  { env with flags := Flags.restore env.flags saved mask }
def testFlags (env : Env) (mask : Flags) : Bool := Flags.test env.flags mask
def testSavedFlags (saved mask : Flags) : Bool := Flags.test saved mask

def run (env : Env) (op : RoundingMode → Result α) : α × Env :=
  let result := op env.mode
  (result.value, env.raiseFlags result.flags)

@[simp] theorem run_mode (env : Env) (op : RoundingMode → Result α) :
    (env.run op).2.mode = env.mode := rfl
@[simp] theorem run_value (env : Env) (op : RoundingMode → Result α) :
    (env.run op).1 = (op env.mode).value := rfl

theorem run_sticky (env : Env) (op : RoundingMode → Result α) :
    Flags.LE env.flags (env.run op).2.flags := Flags.le_union_left _ _

/-- Sequential execution and operation-local composition accumulate identical flags. -/
theorem run_bind (env : Env) (op : RoundingMode → Result α)
    (next : α → RoundingMode → Result β) :
    env.run (fun m => (op m).bind (fun a => next a m)) =
      let first := env.run op
      first.2.run (next first.1) := by
  simp [run, raiseFlags, Result.bind, Flags.union_assoc]
end Env
end FP.IEEE
