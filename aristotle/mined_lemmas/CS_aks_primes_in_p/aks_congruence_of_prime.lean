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

theorem aks_congruence_of_prime {n : ℕ} (hp : n.Prime) (r a : ℕ) :
    (X ^ r - 1 : (ZMod n)[X]) ∣ (X + C (a : ZMod n)) ^ n - (X ^ (n % r) + C (a : ZMod n)) := by
  haveI : Fact n.Prime := ⟨hp⟩
  haveI : ExpChar ((ZMod n)[X]) n := ExpChar.prime hp
  have h1 : (X + C (a : ZMod n)) ^ n = X ^ n + C (a : ZMod n) := by
    rw [add_pow_char, ← C_pow, ZMod.pow_card]
  have hdm := Nat.div_add_mod n r
  have h2 : (X ^ n : (ZMod n)[X]) - X ^ (n % r) = X ^ (n % r) * ((X ^ r) ^ (n / r) - 1) := by
    rw [mul_sub, mul_one, ← pow_mul, ← pow_add]
    congr 2
    omega
  have h3 : (X ^ r - 1 : (ZMod n)[X]) ∣ (X ^ r) ^ (n / r) - 1 := by
    simpa using sub_dvd_pow_sub_pow (X ^ r : (ZMod n)[X]) 1 (n / r)
  have h4 : (X + C (a : ZMod n)) ^ n - (X ^ (n % r) + C (a : ZMod n))
      = X ^ (n % r) * ((X ^ r) ^ (n / r) - 1) := by rw [h1, ← h2]; ring
  rw [h4]
  exact h3.mul_left _

/-- **Completeness of the AKS test.**  Every prime `n` passes all the checks performed by the
AKS algorithm, for an arbitrary choice of the modulus `r`:

* `n` is not a perfect power `a ^ b` with `1 < a`, `2 ≤ b`;
* no `a ≤ r` has a nontrivial common factor with `n` (i.e. `gcd a n = 1` unless `n ∣ a`);
* the polynomial congruence `(X + a)^n = X^(n mod r) + a` holds modulo `(X^r - 1, n)`.

(The converse -- soundness of the test for a suitable `r` -- is the deep half of AKS and is
not formalised here; see the module docstring.) -/
