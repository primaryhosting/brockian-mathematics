/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Euclid's algorithm on the natural numbers: `euclid a b` repeatedly replaces
the pair `(a, b)` by `(b % a, a)` until the first component is `0`.

The definition is accepted by Lean only together with a termination proof: the
first argument strictly decreases at each recursive call, since `b % a < a`
whenever `a ≠ 0`. Hence `euclid` is a total function — the algorithm terminates
on every input. -/

theorem euclid_of_ne_zero (a b : Nat) (h : a ≠ 0) : euclid a b = euclid (b % a) a := by
  rw [euclid]; simp [h]

/-- **Correctness of Euclid's algorithm**: for all natural numbers `a` and `b`,
the (terminating) algorithm `euclid` returns `gcd a b`. -/
