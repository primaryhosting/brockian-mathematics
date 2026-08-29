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

lemma sum_nthRootsFinset_eq_zero : ∑ x ∈ nthRootsFinset 11 (1 : ℂ), x = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 11), Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  rw [nthRootsFinset_eq_image_pow hζ,
    Finset.sum_image (fun i hi j hj hij => hζ.pow_inj (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj) hij)]
  exact hζ.geom_sum_eq_zero (by norm_num)

/-- The 11-th roots of unity split as `{1}` together with the primitive ones. -/
