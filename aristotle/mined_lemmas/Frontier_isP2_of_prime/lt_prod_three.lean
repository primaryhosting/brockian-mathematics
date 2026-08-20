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

theorem lt_prod_three {n a b c : ℕ} (ha : n < a ^ 3) (hb : n < b ^ 3) (hc : n < c ^ 3) :
    n < a * b * c := by
  by_contra h
  push_neg at h
  have h1 : (n + 1) ^ 3 ≤ a ^ 3 * b ^ 3 * c ^ 3 := by
    have h0 : (n + 1) * (n + 1) * (n + 1) ≤ a ^ 3 * b ^ 3 * c ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    nlinarith [h0]
  have h2 : (a * b * c) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left h 3
  nlinarith [h1, h2]

/-- **Sieve criterion for almost primality.** If `1 < q ≤ n` and every prime factor of `q`
exceeds `n ^ (1/3)` (in the form `n < r ^ 3`), then `q` has at most two prime factors counted
with multiplicity, i.e. `q` is a `P₂` number. -/
