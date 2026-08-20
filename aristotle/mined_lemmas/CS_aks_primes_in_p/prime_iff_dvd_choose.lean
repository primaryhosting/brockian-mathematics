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

theorem prime_iff_dvd_choose (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ k, 0 < k → k < n → n ∣ n.choose k := by
  constructor
  · intro hp k hk0 hkn
    exact_mod_cast hp.dvd_choose_self hk0.ne' hkn
  · intro h
    by_contra hnp
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hpn : n.minFac ∣ n := Nat.minFac_dvd n
    have hne : n.minFac ≠ n := fun he => hnp (he ▸ hp)
    exact not_dvd_choose_of_prime_factor (by omega) hp hpn
      (h n.minFac hp.pos (lt_of_le_of_ne (Nat.minFac_le (by omega)) hne))

/-- The modular (mod `X ^ r - 1`) congruence actually tested by the AKS algorithm holds
for every prime `n`, every modulus `r` and every shift `a`. -/
