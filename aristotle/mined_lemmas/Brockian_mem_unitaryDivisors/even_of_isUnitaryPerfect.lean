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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem even_of_isUnitaryPerfect {n : ℕ} (hn : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hsig⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hodd
  have h2n : ¬ (2 ∣ n) := by rw [Nat.even_iff] at hodd; omega
  have hprod : usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := usigma_eq_prod hn0
  have hdvd : 2 ^ n.primeFactors.card ∣ usigma n := by
    rw [hprod, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpne : p ≠ 2 := by rintro rfl; exact h2n (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k, hk⟩ := (hpp.odd_of_ne_two hpne).pow (n := n.factorization p)
    exact ⟨k + 1, by omega⟩
  have hcard : n.primeFactors.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (4 : ℕ) ∣ 2 * n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hc
        _ ∣ usigma n := hdvd
        _ = 2 * n := hsig
    obtain ⟨c, hcc⟩ := h4
    exact h2n ⟨c, by omega⟩
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    prod_primeFactors_pow_factorization hn0
  interval_cases hcards : n.primeFactors.card
  · rw [Finset.card_eq_zero] at hcards
    rw [hcards, Finset.prod_empty] at hself
    rw [← hself] at hsig
    simp at hsig
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcards
    rw [hp, Finset.prod_singleton] at hself hprod
    rw [hprod, hself] at hsig
    have hn1 : n = 1 := by omega
    rw [hn1] at hp
    simp at hp

