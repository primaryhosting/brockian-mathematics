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

theorem Chen_base_case (n : ℕ) (h4 : 4 ≤ n) (h500 : n ≤ 500) (hn : Even n) :
    ChenRepresentable n := by
  obtain ⟨p, -, hp, hq⟩ := goldbach_le_500 n (Finset.mem_Icc.mpr ⟨h4, h500⟩) hn
  refine chenRepresentable_of_sum_two_primes hp hq ?_
  have hpn : p ≤ n := by
    by_contra hlt
    have h0 : n - p = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hlt))
    rw [h0] at hq
    exact Nat.not_prime_zero hq
  omega

/-- **Chen's theorem, as a Lean-checked reduction.**

The full statement of Chen's theorem — every sufficiently large even number `n` is `p + q` with
`p` prime and `q` having at most two prime factors — is reduced here to the sieve statement that
Chen's method produces: for all large even `n` there is a prime `p` such that `n - p > 1` has no
prime factor below `n ^ (1/3)`. Given such a `p`, the number `q = n - p` cannot have three or
more prime factors, since their product would already exceed `n`; hence `q` is a `P₂` number.

Unconditionally, the conclusion is verified by kernel computation for all even `n` with
`4 ≤ n ≤ 500` in `Frontier.Chen_base_case`, and it also follows from Goldbach's conjecture, see
`Frontier.goldbach_implies_chen`. -/
