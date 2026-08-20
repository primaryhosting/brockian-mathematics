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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A *Giuga number* is a composite natural number `n > 1` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/

theorem sum_inv_le_B :
    ∀ (k : ℕ), k ≤ 8 → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ k →
      ∑ p ∈ S, (1 : ℚ) / p ≤ B k := by
  intro k
  induction k with
  | zero =>
    intro _ S _ hc
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
    simp [hS0, B]
  | succ k ih =>
    intro hk S hS hc
    have hqpos : (0 : ℚ) < q k := by
      have := q_ge_three k
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    have hBsucc : B (k + 1) = B k + 1 / q k := by
      simp [B, Finset.sum_range_succ]
    rcases le_or_gt S.card k with hcase | hcase
    · have hpos : (0 : ℚ) < 1 / q k := by positivity
      linarith [ih (by omega) S hS hcase]
    · have hcard : S.card = k + 1 := le_antisymm hc hcase
      obtain ⟨hne, hmax⟩ := le_max_of_odd_primes k (by omega) S hS hcard
      have hmS : S.max' hne ∈ S := S.max'_mem hne
      have hsplit : ∑ p ∈ S, (1 : ℚ) / p
          = 1 / (S.max' hne : ℚ) + ∑ p ∈ S.erase (S.max' hne), (1 : ℚ) / p :=
        (Finset.add_sum_erase _ _ hmS).symm
      have h1 : (1 : ℚ) / (S.max' hne : ℚ) ≤ 1 / q k := by
        apply one_div_le_one_div_of_le hqpos
        exact_mod_cast hmax
      have h2 : ∑ p ∈ S.erase (S.max' hne), (1 : ℚ) / p ≤ B k := by
        refine ih (by omega) _ (fun p hp => hS p (Finset.mem_of_mem_erase hp)) ?_
        rw [Finset.card_erase_of_mem hmS, hcard]
        omega
      linarith [hsplit, h1, h2]

