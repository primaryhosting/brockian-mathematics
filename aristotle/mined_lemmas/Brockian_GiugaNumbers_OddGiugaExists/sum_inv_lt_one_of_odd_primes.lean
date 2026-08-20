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

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem sum_inv_lt_one_of_odd_primes {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (h2 : ∀ p ∈ S, p ≠ 2) (hcard : S.card ≤ 8) :
    ∑ p ∈ S, (p : ℚ)⁻¹ < 1 := by
  classical
  set L : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23} with hL
  set A : Finset ℕ := S.filter (fun p => p < 29) with hA
  set B : Finset ℕ := S.filter (fun p => ¬ p < 29) with hB
  have hAL : A ⊆ L := by
    intro p hpA
    rw [hA, Finset.mem_filter] at hpA
    obtain ⟨hpS, hlt⟩ := hpA
    have hpp := hp p hpS
    have hp2 := h2 p hpS
    have h2le : 2 ≤ p := hpp.two_le
    rw [hL]
    interval_cases p <;> revert hpp hp2 <;> decide
  have hsplit : ∑ p ∈ S, (p : ℚ)⁻¹ = (∑ p ∈ A, (p : ℚ)⁻¹) + ∑ p ∈ B, (p : ℚ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hBbound : ∑ p ∈ B, (p : ℚ)⁻¹ ≤ (B.card : ℚ) * (1 / 29) := by
    have hmem : ∀ p ∈ B, (p : ℚ)⁻¹ ≤ 1 / 29 := by
      intro p hpB
      rw [hB, Finset.mem_filter] at hpB
      have h29 : (29 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 29 ≤ p)
      rw [one_div]
      exact inv_anti₀ (by norm_num) h29
    calc ∑ p ∈ B, (p : ℚ)⁻¹ ≤ B.card • (1 / 29 : ℚ) := Finset.sum_le_card_nsmul B _ _ hmem
      _ = (B.card : ℚ) * (1 / 29) := by simp [nsmul_eq_mul]
  have hLAbound : (B.card : ℚ) * (1 / 23) ≤ ∑ p ∈ L \ A, (p : ℚ)⁻¹ := by
    have hmem : ∀ p ∈ L \ A, (1 / 23 : ℚ) ≤ (p : ℚ)⁻¹ := by
      intro p hpm
      have hpL : p ∈ L := (Finset.mem_sdiff.1 hpm).1
      have hple : 3 ≤ p ∧ p ≤ 23 := by
        rw [hL] at hpL
        fin_cases hpL <;> omega
      have h1 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      have h2' : (p : ℚ) ≤ 23 := by exact_mod_cast hple.2
      rw [one_div]
      exact inv_anti₀ h1 h2'
    have hcards : B.card ≤ (L \ A).card := by
      have hLcard : L.card = 8 := by rw [hL]; decide
      have hAcard : A.card ≤ 8 := le_trans (Finset.card_filter_le _ _) hcard
      have hsd : (L \ A).card = L.card - A.card := Finset.card_sdiff_of_subset hAL
      have hAB : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
      omega
    have hcast : (B.card : ℚ) ≤ ((L \ A).card : ℚ) := by exact_mod_cast hcards
    calc (B.card : ℚ) * (1 / 23) ≤ ((L \ A).card : ℚ) * (1 / 23) := by linarith
      _ = (L \ A).card • (1 / 23 : ℚ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ L \ A, (p : ℚ)⁻¹ := Finset.card_nsmul_le_sum _ _ _ hmem
  have hAeq : ∑ p ∈ A, (p : ℚ)⁻¹ = (∑ p ∈ L, (p : ℚ)⁻¹) - ∑ p ∈ L \ A, (p : ℚ)⁻¹ := by
    have h := Finset.sum_sdiff_eq_sub (f := fun p : ℕ => (p : ℚ)⁻¹) hAL
    linarith [h]
  have hLsum : ∑ p ∈ L, (p : ℚ)⁻¹ < 1 := by
    rw [hL]
    norm_num
  have hBnn : (0 : ℚ) ≤ (B.card : ℚ) := by positivity
  rw [hsplit, hAeq]
  linarith [hBbound, hLAbound, hLsum, hBnn]

/-- The prime factors of a Giuga number multiply back to it. -/
