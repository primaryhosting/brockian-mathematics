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

theorem lexNat_succSucc_inner (m n v : Nat) : LexNat (m, v) (m + 1, n + 1) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The two-argument Ackermann function, defined by well-founded recursion on the pair of its
arguments ordered lexicographically. -/
