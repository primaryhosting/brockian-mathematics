import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Polynomial

namespace Math

/-- The sum of the primitive `7`-th roots of unity in `ℂ` equals `μ 7 = -1`.

The primitive `7`-th roots are exactly `ζ ^ i` for `1 ≤ i < 7`, where
`ζ = exp (2 π i / 7)` (`Complex.isPrimitiveRoot_exp`), since `7` is prime.
Their sum is `(∑ i ∈ range 7, ζ ^ i) - 1 = -1` by
`IsPrimitiveRoot.geom_sum_eq_zero`, and `μ 7 = -1` by
`ArithmeticFunction.moebius_apply_prime`. -/
theorem mobius_root_sum_7 :
    ∑ ζ ∈ primitiveRoots 7 ℂ, ζ = (ArithmeticFunction.moebius 7 : ℂ) := by
  have hζ := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have key : primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro hx
      have hp : IsPrimitiveRoot x 7 := isPrimitiveRoot_of_mem_primitiveRoots hx
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hp.pow_eq_one
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      rcases Nat.eq_zero_or_pos i with rfl | h
      · rw [pow_zero] at hp
        simpa using hp.unique IsPrimitiveRoot.one
      · exact h
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      rw [mem_primitiveRoots (by norm_num)]
      refine hζ.pow_of_coprime i ?_
      interval_cases i <;> decide
  rw [key, Finset.sum_image (by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 hij)]
  have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.Ico 1 7, ζ ^ i = (∑ i ∈ Finset.range 7, ζ ^ i) - 1 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0 : ℕ) < 7)]
    simp
  rw [hsplit, hgeom, ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

end Math

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

