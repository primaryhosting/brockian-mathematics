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
theorem aks_criterion (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a : ZMod n, (X + C a) ^ n = X ^ n + C a := by
  constructor
  · intro hp a
    haveI : Fact n.Prime := ⟨hp⟩
    haveI : ExpChar ((ZMod n)[X]) n := ExpChar.prime hp
    rw [add_pow_char, ← C_pow, ZMod.pow_card]
  · intro h
    by_contra hnp
    set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hne : p ≠ n := fun he => hnp (he ▸ hp)
    have h1 := h 1
    rw [map_one] at h1
    have hc := congrArg (fun q => Polynomial.coeff q p) h1
    simp only [coeff_X_add_one_pow, coeff_add, coeff_X_pow, coeff_one, hne, if_false,
      hp.ne_zero, if_false] at hc
    have hdvd : n ∣ n.choose p := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hc)
    exact not_dvd_choose_of_prime_factor (by omega) hp hpn hdvd

/-- The same criterion, in the equivalent binomial-coefficient form: `n ≥ 2` is prime
iff `n` divides all the "interior" binomial coefficients `n.choose k`, `0 < k < n`. -/
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
theorem aks_primes_in_p (n : ℕ) (hn : 2 ≤ n) :
    (n.Prime ↔ ∀ a : ZMod n, (X + C a) ^ n = X ^ n + C a) ∧
    (n.Prime ↔ ∀ k, 0 < k → k < n → n ∣ n.choose k) :=
  ⟨aks_criterion n hn, prime_iff_dvd_choose n hn⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

