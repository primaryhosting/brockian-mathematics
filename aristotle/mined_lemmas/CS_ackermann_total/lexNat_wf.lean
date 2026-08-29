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

theorem lexNat_wf : WellFounded LexNat :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- The recursive call `A m 1` made by `A (m+1) 0` decreases in the lexicographic order. -/
