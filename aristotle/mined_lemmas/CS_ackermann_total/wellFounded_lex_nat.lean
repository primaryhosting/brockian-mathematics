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

theorem wellFounded_lex_nat :
    WellFounded (Prod.Lex (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Existence: the value `ack m n` satisfies the Ackermann equations at `(m, n)`. -/
