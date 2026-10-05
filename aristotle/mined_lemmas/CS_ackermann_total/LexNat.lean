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

def LexNat : Nat × Nat → Nat × Nat → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- The lexicographic order on `Nat × Nat` is well-founded. -/
