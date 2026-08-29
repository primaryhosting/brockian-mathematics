/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Polynomial

namespace Math

/-- The set of primitive `7`-th roots of unity in `ℂ` is the image of `{1, …, 6}` under
`i ↦ ζ ^ i`, where `ζ` is any primitive `7`-th root of unity. -/

lemma sum_primitiveRoots_seven : ∑ x ∈ primitiveRoots 7 ℂ, x = -1 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  rw [primitiveRoots_seven_eq_image hζ, Finset.sum_image]
  · have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 7)] at hgeom
    simp only [pow_zero] at hgeom
    linear_combination hgeom
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 hij

/-- The sum of the primitive 7-th roots of unity equals `μ(7)`. -/
