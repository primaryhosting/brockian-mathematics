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
