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

/-
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Cullen primes (primes of the form `n * 2 ^ n + 1`) is an open
problem.  This file gives a Lean-checked *conditional reduction*: the infinitude of
Cullen primes follows from the existence of arbitrarily large odd `n` admitting a
Proth witness, i.e. an `a` with `a ^ ((n * 2 ^ n) / 2) = -1` modulo `n * 2 ^ n + 1`.
This is exactly the criterion (Proth's theorem, proved here from scratch) that is
used in practice to certify Cullen primes, and for odd `n` the condition is in fact
*equivalent* to primality of the Cullen number.

The file also contains unconditional results in the opposite direction: every odd
prime `p` divides the Cullen number `cullen (p - 2)`, hence infinitely many Cullen
numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem proth_prime_of_pow_eq_neg_one {k m : ℕ} (hk : Odd k) (hkm : k < 2 ^ m)
    (hm : 0 < m) (a : ZMod (k * 2 ^ m + 1)) (ha : a ^ (k * 2 ^ (m - 1)) = -1) :
    (k * 2 ^ m + 1).Prime := by
  have hk1 : 1 ≤ k := hk.pos
  have h2pos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hmm : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
  have h2m : 2 ^ (m - 1) * 2 = 2 ^ m := by rw [← pow_succ, hmm]
  have hNodd : ¬ (2 ∣ k * 2 ^ m + 1) := by
    have : 2 ∣ k * 2 ^ m := ⟨k * 2 ^ (m - 1), by rw [← h2m]; ring⟩
    omega
  have key : ∀ p : ℕ, p.Prime → p ∣ (k * 2 ^ m + 1) → 2 ^ m < p := by
    intro p hp hpd
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by rintro rfl; exact hNodd hpd
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    haveI : Fact (2 < p) := ⟨hp3⟩
    set f := ZMod.castHom hpd (ZMod p) with hf
    set c : ZMod p := (f a) ^ k with hc
    have hcpow : c ^ 2 ^ (m - 1) = -1 := by
      rw [hc, ← pow_mul, ← map_pow, ha, map_neg, map_one]
    have hcpow2 : c ^ 2 ^ (m - 1 + 1) = 1 := by
      rw [pow_succ, pow_mul, hcpow]; simp
    have hne : ¬ c ^ 2 ^ (m - 1) = 1 := by
      rw [hcpow]; exact ZMod.neg_one_ne_one
    have hord : orderOf c = 2 ^ (m - 1 + 1) := orderOf_eq_prime_pow hne hcpow2
    rw [hmm] at hord
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_pow (by positivity)] at hcpow
      exact one_ne_zero (α := ZMod p) (by linear_combination hcpow)
    have hdvd : 2 ^ m ∣ p - 1 :=
      hord ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hc0)
    have : 2 ^ m ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by positivity) hnp
  have hN1 : k * 2 ^ m + 1 ≠ 1 := by nlinarith
  have hmf := Nat.minFac_prime hN1
  have hlt := key _ hmf (Nat.minFac_dvd _)
  nlinarith [hsq, hlt, hkm]

/-- For `0 < n`, the halved predecessor of a Cullen number is `n * 2 ^ (n - 1)`. -/
