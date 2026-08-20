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

def euclid (a b : Nat) : Nat :=
  if a = 0 then b else euclid (b % a) a
decreasing_by
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

theorem euclid_of_ne_zero (a b : Nat) (h : a ≠ 0) : euclid a b = euclid (b % a) a := by
  rw [euclid]; simp [h]

/-- **Correctness of Euclid's algorithm**: for all natural numbers `a` and `b`,
the (terminating) algorithm `euclid` returns `gcd a b`. -/

theorem euclid_gcd_correct (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction a, b using euclid.induct with
  | case1 b => simp
  | case2 a b h ih => rw [euclid_of_ne_zero a b h, Nat.gcd_rec, ih]

/-- The value returned by Euclid's algorithm is a greatest common divisor: it
divides both inputs, and every common divisor of the inputs divides it. -/
