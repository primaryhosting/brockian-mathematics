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

theorem lexNat_succSucc_outer (m n : Nat) : LexNat (m + 1, n) (m + 1, n + 1) :=
  Prod.Lex.right _ (Nat.lt_succ_self n)

/-- The inner recursive call `A m v` made by `A (m+1) (n+1)` decreases lexicographically,
whatever the value `v` computed by the outer call. -/
