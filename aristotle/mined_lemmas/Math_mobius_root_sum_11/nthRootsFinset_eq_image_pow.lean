/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Polynomial

namespace Math

/-- The 11-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `i < 11`, of a primitive
one. -/

lemma nthRootsFinset_eq_image_pow {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    nthRootsFinset 11 (1 : ℂ) = (Finset.range 11).image (fun i => ζ ^ i) := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rw [Polynomial.mem_nthRootsFinset (by norm_num)]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [hζ.card_nthRootsFinset]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    exact hζ.pow_inj hi hj hij

/-- The sum of all 11-th roots of unity in `ℂ` is `0`. -/
