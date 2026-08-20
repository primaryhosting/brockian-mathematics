/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- The lexicographic order on `Nat × Nat` is well founded.  This is the termination
measure that justifies the recursive definition of the Ackermann function.  It follows
from the existing library lemma `Prod.lexAccessible` together with the well-foundedness
of `<` on `Nat` (`Nat.lt_wfRel`). -/

theorem ack_eq_nat_ack : ∀ m n : ℕ, ack m n = _root_.ack m n
  | 0, n => by rw [ack_zero, _root_.ack_zero]
  | m + 1, 0 => by rw [ack_succ_zero, _root_.ack_succ_zero, ack_eq_nat_ack m 1]
  | m + 1, n + 1 => by
      rw [ack_succ_succ, _root_.ack_succ_succ, ack_eq_nat_ack (m + 1) n,
        ack_eq_nat_ack m (_root_.ack (m + 1) n)]
  termination_by m n => (m, n)

/-- Totality of the Ackermann function, stated with Mathlib's `∃!`. -/
