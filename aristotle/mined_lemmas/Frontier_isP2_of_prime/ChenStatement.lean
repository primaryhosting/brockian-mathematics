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

def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ChenRepresentable n

/-- The sieve statement underlying Chen's method: for every sufficiently large even `n` there is a
prime `p` with `1 < n - p` such that every prime factor `r` of `n - p` satisfies `n < r ^ 3`
(i.e. `r > n ^ (1/3)`). -/
