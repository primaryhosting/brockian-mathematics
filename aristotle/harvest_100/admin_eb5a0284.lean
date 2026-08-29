-- (Lean requires `import` to be the first command, so the required header is
-- reproduced here as a line comment and again as a module docstring below.)
-- /-!
-- # Mobius Root Sum 8
-- Category: Pure Mathematics
-- Target: Math.mobius_root_sum_8
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- A primitive 8-th root of unity `ζ` satisfies `ζ ^ 4 = -1`. -/
theorem pow_four_eq_neg_one_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    ζ ^ 4 = -1 := by
  have h8 : ζ ^ 8 = 1 := h.pow_eq_one
  have hfac : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  · linear_combination h2

/-- The negative of a primitive 8-th root of unity is again a primitive 8-th root of unity. -/
theorem isPrimitiveRoot_neg_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    IsPrimitiveRoot (-ζ) 8 := by
  have h5 : IsPrimitiveRoot (ζ ^ 5) 8 := h.pow_of_coprime 5 (by decide)
  have hz : ζ ^ 5 = -ζ := by
    have := pow_four_eq_neg_one_of_isPrimitiveRoot_eight h
    calc ζ ^ 5 = ζ ^ 4 * ζ := by ring
    _ = -ζ := by rw [this]; ring
  rwa [hz] at h5

/-- Negation is a bijection of the set of primitive 8-th roots of unity in `ℂ`. -/
theorem image_neg_primitiveRoots_eight :
    (primitiveRoots 8 ℂ).image (fun z : ℂ => -z) = primitiveRoots 8 ℂ := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_primitiveRoots (by norm_num)).mpr
      (isPrimitiveRoot_neg_of_isPrimitiveRoot_eight ((mem_primitiveRoots (by norm_num)).mp hw))
  · intro hz
    refine ⟨-z, ?_, by ring⟩
    exact (mem_primitiveRoots (by norm_num)).mpr
      (isPrimitiveRoot_neg_of_isPrimitiveRoot_eight ((mem_primitiveRoots (by norm_num)).mp hz))

/-- The sum of the primitive 8-th roots of unity equals `μ 8`. -/
theorem mobius_root_sum_8 :
    ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 8 : ℂ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)]
    norm_num
  have hinj : Set.InjOn (fun z : ℂ => -z) (primitiveRoots 8 ℂ) := fun a _ b _ hab => by
    simpa using neg_injective hab
  have key : ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = -∑ ζ ∈ primitiveRoots 8 ℂ, ζ := by
    conv_lhs => rw [← image_neg_primitiveRoots_eight]
    rw [Finset.sum_image hinj, Finset.sum_neg_distrib]
  rw [hmu]
  linear_combination key / 2

end Math

