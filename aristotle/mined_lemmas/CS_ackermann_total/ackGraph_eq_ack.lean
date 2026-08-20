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

theorem ackGraph_eq_ack {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => rw [ack_zero]
  | succZero _ ih => rw [ack_succ_zero]; exact ih
  | succSucc _ _ ih₁ ih₂ => subst ih₁; rw [ack_succ_succ]; exact ih₂

/-- **The Ackermann function is total.**  For every pair `(m, n)` of naturals there is a
(unique) value satisfying the Ackermann recurrences

* `A 0 n = n + 1`,
* `A (m+1) 0 = A m 1`,
* `A (m+1) (n+1) = A m (A (m+1) n)`.

The recursion terminates because the lexicographic order on `Nat × Nat` is well founded
(`lex_nat_nat_wellFounded`), and `ack` is the total function realising it. -/
