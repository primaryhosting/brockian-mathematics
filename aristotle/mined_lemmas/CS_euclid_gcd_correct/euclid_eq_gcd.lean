/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- **Euclid's algorithm.**  On input `(a, b)` it returns `b` when `a = 0`, and otherwise
recurses on `(b % a, a)`.  The recursion is well founded: the first argument strictly
decreases at every step (`b % (a+1) < a+1`), which is exactly the termination argument
discharged by `decreasing_by` below.  Consequently `euclid` is a total function, i.e. the
algorithm terminates on every input. -/

theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  fun_induction euclid a b with
  | case1 b => rw [Nat.gcd_zero_left]
  | case2 n b ih => rw [ih]; exact (Nat.gcd_rec (n + 1) b).symm

/--
**Correctness (and termination) of Euclid's algorithm.**

`CS.euclid` is defined by well-founded recursion on its first argument, which strictly
decreases at each recursive call (see `CS.euclid_measure_decreases`); hence it is a
total function and the algorithm terminates on all inputs.

This theorem states that the value it returns really is `gcd a b`: it coincides with
`Nat.gcd a b`, it is a common divisor of `a` and `b`, and every common divisor of `a`
and `b` divides it — i.e. it is the greatest common divisor.
-/
