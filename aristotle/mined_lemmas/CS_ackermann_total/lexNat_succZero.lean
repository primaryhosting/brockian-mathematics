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

theorem lexNat_succZero (m : Nat) : LexNat (m, 1) (m + 1, 0) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The outer recursive call `A (m+1) n` made by `A (m+1) (n+1)` decreases lexicographically. -/
