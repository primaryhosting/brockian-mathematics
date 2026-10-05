/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The Ackermann function, defined by recursion on the lexicographic order on `Nat × Nat`.

Lean accepts this definition precisely because each recursive call decreases the argument pair
in that (well-founded) order:
`(m, 1) <ₗ (m+1, 0)`, `(m+1, n) <ₗ (m+1, n+1)` and `(m, ack (m+1) n) <ₗ (m+1, n+1)`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by simp [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by simp [ack]

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by simp [ack]

/-- The lexicographic order on `Nat × Nat`, the termination measure of the Ackermann
recursion, is well-founded.  (This is `Prod.lex`, the standard library's well-founded
lexicographic combination of two well-founded relations.) -/
theorem lex_nat_wellFounded :
    WellFounded (Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- **The Ackermann function is total** (well-founded on lexicographic `Nat × Nat`).

Two things are asserted:

* the recursion measure, the lexicographic order on `Nat × Nat`, is well-founded;
* there exists a *total* function `f : Nat → Nat → Nat` (i.e. a genuine element of the
  function type, defined at every pair of arguments) satisfying the three defining
  equations of the Ackermann function.

The witness is `CS.ack`, which Lean elaborates by well-founded recursion on exactly this
lexicographic order; totality is therefore witnessed by the existence of the term itself,
and the equations are its recursion equations (`ack_zero`, `ack_succ_zero`, `ack_succ_succ`).

Mathlib also provides this function as `ack` (in `Mathlib.Computability.Ackermann`), with the
same three equations `ack_zero`, `ack_succ_zero`, `ack_succ_succ`; the development here is
kept import-free and self-contained. -/
theorem ackermann_total :
    WellFounded (Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·)) ∧
      ∃ f : Nat → Nat → Nat,
        (∀ n, f 0 n = n + 1) ∧
        (∀ m, f (m + 1) 0 = f m 1) ∧
        (∀ m n, f (m + 1) (n + 1) = f m (f (m + 1) n)) :=
  ⟨lex_nat_wellFounded, ack, ack_zero, ack_succ_zero, ack_succ_succ⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import RequestProject.CS

/-!
Companion file: `CS.ack` agrees with Mathlib's `ack`
(`Mathlib.Computability.Ackermann`), which is defined by well-founded recursion on the same
lexicographic order.
-/

namespace CS

theorem ack_eq_mathlib_ack : ∀ m n, CS.ack m n = _root_.ack m n
  | 0, n => by simp
  | m + 1, 0 => by
      simp [ack_eq_mathlib_ack m 1]
  | m + 1, n + 1 => by
      rw [CS.ack_succ_succ, _root_.ack_succ_succ, ack_eq_mathlib_ack (m + 1) n,
        ack_eq_mathlib_ack m _]

end CS

