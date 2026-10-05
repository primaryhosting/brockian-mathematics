/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma sum_chi_mul_chi {n : ℕ} (x y : Fin n → Bool) :
    (∑ S : Finset (Fin n), chi S x * chi S y) = if x = y then (2 : ℤ) ^ n else 0 := by
  have key : ∀ S : Finset (Fin n), chi S x * chi S y
      = ∏ i ∈ S, ((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)) := by
    intro S
    rw [chi, chi, ← Finset.prod_mul_distrib]
  simp only [key]
  have h2 : ∏ i : Fin n, (((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)) + 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∏ i ∈ S, ((if x i then (-1 : ℤ) else 1) * (if y i then (-1 : ℤ) else 1)))
          * ∏ _i ∈ Finset.univ \ S, (1 : ℤ) := Finset.prod_add _ _ _
  simp only [Finset.prod_const_one, mul_one, Finset.powerset_univ] at h2
  rw [← h2]
  by_cases hxy : x = y
  · subst hxy
    have hall : ∀ i : Fin n,
        (((if x i then (-1 : ℤ) else 1) * (if x i then (-1 : ℤ) else 1)) + 1) = 2 := by
      intro i; cases x i <;> norm_num
    rw [Finset.prod_congr rfl (fun i _ => hall i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      exact hxy (funext fun i => not_not.1 (fun hh => h ⟨i, hh⟩))
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    revert hi
    cases hx : x i <;> cases hy : y i <;> simp

/-- Summed over the cube, a character is `2^n` for `S = ∅` and `0` otherwise. -/
