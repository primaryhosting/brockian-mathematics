import Mathlib
import RequestProject.Main

/-!
# Link with Mathlib's Ackermann function

The Ackermann function `CS.ack` defined in `RequestProject.Main` agrees with
Mathlib's `ack` from `Mathlib/Computability/Ackermann.lean`. Consequently the
totality statement `CS.ackermann_total` also characterises Mathlib's `ack`.
-/

set_option autoImplicit false

namespace CS


theorem lex_decreasing_succ_zero (m : Nat) :
    Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·) (m, 1) (m + 1, 0) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The inner recursive call of the Ackermann recursion decreases the lexicographic
measure. -/
