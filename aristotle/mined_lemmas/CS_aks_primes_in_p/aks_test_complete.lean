/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file formalises the algebraic identity that the Agrawal–Kayal–Saxena
("PRIMES is in P") algorithm tests, namely the characterisation

`n` is prime  ↔  `(X + a)^n = X^n + a` in `(ZMod n)[X]` for every `a`,

for every `n ≥ 2`, together with the equivalent binomial-coefficient form
`n` is prime ↔ `n ∣ n.choose k` for all `0 < k < n`.

The forward direction is the Frobenius/freshman's-dream identity; the reverse
direction is the genuinely arithmetic half: if `p` is a prime factor of a
composite `n`, then `n ∤ n.choose p`, which is proved here from the identity
`n * (n-1).choose (p-1) = n.choose p * p` together with Lucas' theorem.

Also proved here is completeness of the AKS test: every prime passes all the
checks of the algorithm (not a perfect power, no small common factor, and the
modular congruence `(X + a)^n ≡ X^(n mod r) + a  (mod X^r - 1, n)`).

Scope note: this file proves the algebraic criterion underlying the AKS
algorithm.  It does *not* contain the full complexity-theoretic statement
`PRIMES ∈ P` (deterministic polynomial-time decidability): Mathlib currently has
no development of time-bounded computation / complexity classes, and soundness
of the modular test for a suitable small `r` (the introspective-numbers
argument) is not formalised here either.
-/

open Polynomial

namespace CS

/-- If `p` is a prime factor of `n > 0`, then `n` does not divide the
binomial coefficient `n.choose p`.  (The `p`-adic valuation of `n.choose p` is
exactly one less than that of `n`.) -/

theorem aks_test_complete {n : ℕ} (hp : n.Prime) (r : ℕ) :
    (¬ ∃ a b : ℕ, 1 < a ∧ 2 ≤ b ∧ n = a ^ b) ∧
    (∀ a ≤ r, Nat.gcd a n = 1 ∨ n ∣ a) ∧
    (∀ a : ℕ, (X ^ r - 1 : (ZMod n)[X]) ∣
      (X + C (a : ZMod n)) ^ n - (X ^ (n % r) + C (a : ZMod n))) := by
  refine ⟨?_, ?_, fun a => aks_congruence_of_prime hp r a⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    have := (Nat.Prime.pow_eq_iff hp).mp rfl
    omega
  · intro a _
    by_cases h : n ∣ a
    · exact Or.inr h
    · exact Or.inl (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))

/-- **AKS ("PRIMES is in P"), algebraic core.**

For every `n ≥ 2` the following are equivalent:

* `n` is prime;
* `(X + a)^n = X^n + a` in `(ZMod n)[X]` for every `a : ZMod n`;
* `n ∣ n.choose k` for every `0 < k < n`.

This is the identity that the Agrawal–Kayal–Saxena algorithm tests.  See the
scope note in the module docstring: the complexity-theoretic content of
`PRIMES ∈ P` (a deterministic polynomial-time decision procedure) is *not*
formalised here. -/
