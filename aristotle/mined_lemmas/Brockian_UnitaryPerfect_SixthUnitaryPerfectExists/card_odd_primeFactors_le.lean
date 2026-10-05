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

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/

lemma card_odd_primeFactors_le {n : ℕ} (h : IsUnitaryPerfect n) :
    (n.primeFactors.erase 2).card ≤ n.factorization 2 + 1 := by
  obtain ⟨hpos, heq⟩ := h
  have hn : n ≠ 0 := hpos.ne'
  set k := (n.primeFactors.erase 2).card with hk
  -- `2 ^ k` divides the odd part of the product formula
  have hdvd_sub : (2 : ℕ) ^ k ∣ ∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1) := by
    rw [hk, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => ?_)
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
    have hpmem : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hodd : Odd p := hpp.odd_of_ne_two hp2
    have : Odd (p ^ n.factorization p) := hodd.pow
    obtain ⟨t, ht⟩ := this
    exact ⟨t + 1, by omega⟩
  have hdvd : (2 : ℕ) ^ k ∣ usigma n := by
    rw [usigma_eq_prod hn]
    exact hdvd_sub.trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _))
  rw [heq] at hdvd
  have h2n : (2 * n) ≠ 0 := by positivity
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h2n).mp hdvd
  rwa [Nat.factorization_mul two_ne_zero hn, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, add_comm] at this

/-- There is no odd unitary perfect number: every unitary perfect number is even. -/
