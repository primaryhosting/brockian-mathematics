/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `Unbdd A` says that the set of naturals satisfying `A` is unbounded, i.e. infinite. -/

theorem le_elt (c : Nat → Nat → Bool) (n : Nat) : n ≤ elt c n := by
  induction n with
  | zero => omega
  | succ n ih => have := elt_lt c (show n < n + 1 by omega); omega

/-- **Infinite Ramsey theorem** for pairs and two colours: every colouring `c` of the
(unordered) pairs of natural numbers with two colours admits an infinite set `S`
all of whose pairs receive the same colour `k`. -/
