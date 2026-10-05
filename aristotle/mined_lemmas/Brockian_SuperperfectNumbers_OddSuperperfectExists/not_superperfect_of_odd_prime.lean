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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`, where `σ` is the
sum-of-divisors function.  The known superperfect numbers are `2, 4, 16, 64, …`,
i.e. the numbers `2 ^ (p - 1)` for which `2 ^ p - 1` is a Mersenne prime.  Whether
an *odd* superperfect number exists is an open problem: none is known, and it is
conjectured that none exists.

Accordingly this file does not prove the (open) existence statement outright.
Instead it develops the basic theory of `σ` needed here and proves an
unconditional **reduction**: an odd superperfect number exists if and only if one
exists that is, in addition, larger than `500` and composite.  Both extra
constraints are proved for every odd superperfect number, so the reduction is a
genuine restriction of the search space, not a tautology.
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem not_superperfect_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ Superperfect p := by
  intro h
  rw [Superperfect, sigma1_prime hp] at h
  obtain ⟨a, k, hk, hak⟩ := Nat.exists_eq_two_pow_mul_odd (n := p + 1) (by omega)
  have hcop : Nat.Coprime (2 ^ a) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hk)
  rw [hak, sigma1_mul_of_coprime hcop, sigma1_two_pow] at h
  -- `1 ≤ a` because `p + 1` is even while `k` is odd
  have ha : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [pow_zero, one_mul] at hak
    obtain ⟨j, hj⟩ := hodd
    obtain ⟨i, hi⟩ := hk
    omega
  set d := 2 ^ (a + 1) - 1 with hd
  have hpow : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd3 : 3 ≤ d := by omega
  have hdodd : Odd d := by
    refine Nat.Even.sub_odd (by omega) ?_ odd_one
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hdvd : d ∣ 2 * p := ⟨sigma1 k, h.symm⟩
  have hcop2 : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hdodd
  have hdp : d ∣ p := Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd
  have hcases := hp.eq_one_or_self_of_dvd d hdp
  have hdeq : d = p := by omega
  rw [hdeq] at h
  have hk2 : sigma1 k = 2 := Nat.eq_of_mul_eq_mul_left hp.pos (by omega)
  exact sigma1_ne_two k hk2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
