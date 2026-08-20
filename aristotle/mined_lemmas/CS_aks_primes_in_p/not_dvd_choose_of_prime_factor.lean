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

theorem not_dvd_choose_of_prime_factor {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) :
    ¬ n ∣ n.choose p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, rfl⟩ := hpn
  have hp2 := hp.two_le
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hpos : 0 < p * (c' + 1) := by positivity
  have hkey : p * (c' + 1) * (p * (c' + 1) - 1).choose (p - 1) = (p * (c' + 1)).choose p * p := by
    have h := Nat.add_one_mul_choose_eq (p * (c' + 1) - 1) (p - 1)
    have e1 : (p * (c' + 1) - 1) + 1 = p * (c' + 1) := by omega
    have e2 : (p - 1) + 1 = p := by omega
    rwa [e1, e2] at h
  rintro ⟨m, hm⟩
  rw [hm] at hkey
  have hdvd : p ∣ (p * (c' + 1) - 1).choose (p - 1) := by
    refine ⟨m, Nat.eq_of_mul_eq_mul_left hpos ?_⟩
    rw [hkey]; ring
  have hn1 : p * (c' + 1) - 1 = p * c' + (p - 1) := by
    have : p * (c' + 1) = p * c' + p := by ring
    omega
  have hmod : (p * (c' + 1) - 1) % p = p - 1 := by
    rw [hn1, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (p * (c' + 1) - 1) / p = c' := by
    rw [hn1, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  have hL := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p * (c' + 1) - 1) (p - 1) p ⟨hp⟩
  rw [hmod, hdiv, Nat.mod_eq_of_lt (show p - 1 < p by omega), Nat.div_eq_of_lt (by omega),
    Nat.choose_self, Nat.choose_zero_right] at hL
  have hz : (p * (c' + 1) - 1).choose (p - 1) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
  have h01 : (0 : ℕ) % p = 1 % p := hz.symm.trans hL
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < p)] at h01
  exact zero_ne_one h01

/-- **The AKS criterion.**  For `n ≥ 2`, the number `n` is prime if and only if the
"freshman's dream" identity `(X + a)^n = X^n + a` holds in `(ZMod n)[X]` for every
`a : ZMod n`.  This is the algebraic identity that the AKS primality test checks
(in the ring `(ZMod n)[X] / (X^r - 1)`, for suitable small `r` and `a`). -/
