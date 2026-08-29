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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite number `n > 1` such that every prime `p` dividing `n`
satisfies `p ∣ n / p - 1`. -/

theorem odd_giuga_nine_le_card_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hsum := h.one_lt_sum_inv
  by_cases h3 : 3 ∈ n.primeFactors
  · have hS' : ∀ p ∈ n.primeFactors.erase 3, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) :=
      fun p hp => primeFactor_props hodd (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    have hcard' : (n.primeFactors.erase 3).card ≤ 7 := by
      rw [Finset.card_erase_of_mem h3]; omega
    have hb := sum_inv_le_of_coprime_six hS'
    have hmono : ∑ i ∈ range (n.primeFactors.erase 3).card, (1 : ℚ) / coprimeSixEnum i
        ≤ ∑ i ∈ range 7, (1 : ℚ) / coprimeSixEnum i := by
      have hsubr : range (n.primeFactors.erase 3).card ⊆ range 7 :=
        Finset.range_subset_range.mpr hcard'
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubr ?_
      intro i _ _
      positivity
    have hsplit : ∑ p ∈ n.primeFactors, (1 : ℚ) / p
        = (1 : ℚ) / 3 + ∑ p ∈ n.primeFactors.erase 3, (1 : ℚ) / p := by
      rw [← Finset.add_sum_erase _ _ h3]
      norm_num
    have hnum : (1 : ℚ) / 3 + ∑ i ∈ range 7, (1 : ℚ) / coprimeSixEnum i < 1 := by
      simp [Finset.sum_range_succ, coprimeSixEnum]
      norm_num
    rw [hsplit] at hsum
    linarith
  · have hS' : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
      intro p hp
      exact primeFactor_props hodd hp (by rintro rfl; exact h3 hp)
    have hcard' : n.primeFactors.card ≤ 8 := by omega
    have hb := sum_inv_le_of_coprime_six hS'
    have hmono : ∑ i ∈ range n.primeFactors.card, (1 : ℚ) / coprimeSixEnum i
        ≤ ∑ i ∈ range 8, (1 : ℚ) / coprimeSixEnum i := by
      have hsubr : range n.primeFactors.card ⊆ range 8 := Finset.range_subset_range.mpr hcard'
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubr ?_
      intro i _ _
      positivity
    have hnum : ∑ i ∈ range 8, (1 : ℚ) / coprimeSixEnum i < 1 := by
      simp [Finset.sum_range_succ, coprimeSixEnum]
      norm_num
    linarith

/-- **Conditional reduction for the existence of an odd Giuga number.**

Whether an odd Giuga number exists is an open problem, so what is proved here is the conditional
statement: if an odd Giuga number exists, then one exists which is moreover squarefree and has at
least nine distinct prime factors. -/
