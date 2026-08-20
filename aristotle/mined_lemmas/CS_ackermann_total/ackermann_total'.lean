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

theorem ackermann_total' (m n : ℕ) : ∃! v : ℕ, AckGraph m n v :=
  ⟨ack m n, ackGraph_ack m n, fun _ hw => ackGraph_eq_ack hw⟩

end CS

