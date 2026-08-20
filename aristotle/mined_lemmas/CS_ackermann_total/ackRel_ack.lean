/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The Ackermann function, defined by recursion on the lexicographic order on `ℕ × ℕ`
(the `termination_by (m, n)` clause below; well-foundedness of that order is recorded
separately as `CS.wellFounded_lex_nat`). -/

theorem ackRel_ack : ∀ m n : Nat, AckRel m n (ack m n)
  | 0, n => by simpa using AckRel.zero n
  | m + 1, 0 => by simpa using AckRel.succ_zero (ackRel_ack m 1)
  | m + 1, n + 1 => by
      simpa using AckRel.succ_succ (ackRel_ack (m + 1) n) (ackRel_ack m (ack (m + 1) n))
termination_by m n => (m, n)

/-- Uniqueness: the Ackermann equations determine at most one value at each argument. -/
