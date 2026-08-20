import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma two_primitive_root_thirteen : IsPrimitiveRootMod 2 13 := by
  have : ((2 : ℤ) : ZMod 13) = (2 : ZMod 13) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

/-- **Artin's conjecture on primitive roots**, formalized, together with everything that
can be established unconditionally about it:

1. the hypothesis "`a` is not a perfect square" is necessary: a square is a primitive
   root modulo no prime other than `2`;
2. the hypothesis "`a ≠ -1`" is necessary: `-1` is a primitive root only modulo `2`
   and `3`;
3. unconditionally, infinitely many primes possess *some* primitive root;
4. base case: `2` is a primitive root modulo `3, 5, 11, 13`, so these primes lie in the
   set that Artin's conjecture asserts to be infinite for `a = 2`;
5. the reduction: the conjecture is equivalent to the assertion that for every admissible
   `a` and every bound `N` there is a prime `p > N` having `a` as a primitive root. -/
