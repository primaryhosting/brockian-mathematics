/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `Nat × Nat`, used as the termination measure for the Ackermann
recursion. -/

theorem cs_ack_eq_ack (m n : ℕ) : CS.ack m n = _root_.ack m n := by
  induction m generalizing n with
  | zero => simp
  | succ m ihm =>
    induction n with
    | zero =>
      rw [CS.ack_succ_zero, _root_.ack_succ_zero]
      exact ihm 1
    | succ n ihn =>
      rw [CS.ack_succ_succ, _root_.ack_succ_succ, ihn]
      exact ihm _

/-- Mathlib's `ack` satisfies the Ackermann recursion. -/
