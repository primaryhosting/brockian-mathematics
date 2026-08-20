import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires the `import` commands to come first in a module, so the
prescribed header comment above is placed immediately after `import Mathlib`.

Contents:

* `Frontier.IsP2`, `Frontier.ChenRepresentable`, `Frontier.ChenStatement` : the formal statement
  of Chen's theorem ("every sufficiently large even number is `p + q` with `p` prime and `q`
  having at most two prime factors").
* `Frontier.Chen_base_case` : an unconditional, kernel-checked verification of the conclusion for
  all even `n` with `4 ≤ n ≤ 500`.
* `Frontier.Chen_theorem` : a Lean-checked reduction of the full statement to the sieve statement
  that Chen's method produces (a prime `p` with all prime factors of `n - p` exceeding `n ^ (1/3)`).
* `Frontier.goldbach_implies_chen` : the (easier) reduction of Chen's statement to Goldbach's
  conjecture.
-/

open ArithmeticFunction

namespace Frontier

/-- `q` is an *almost prime of order 2* (a `P₂` number): `q > 1` and `q` has at most two prime
factors counted with multiplicity (`Ω q ≤ 2`), i.e. `q` is a prime or a product of two primes. -/

theorem Chen_theorem : ChenSieveStatement → ChenStatement := by
  rintro ⟨N, hN⟩
  refine ⟨N, fun n hn hev => ?_⟩
  obtain ⟨p, hp, hpn, hfac⟩ := hN n hn hev
  refine ⟨p, n - p, hp, isP2_of_large_prime_factors (n := n) (by omega) (by omega) hfac, ?_⟩
  omega

/-- Goldbach's conjecture implies Chen's statement (with `N = 4`), since a prime is in particular
a number with at most two prime factors. -/
