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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment rather than a module docstring `/-!`,
-- since Lean 4 requires `import` to precede any module docstring.)

import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/

theorem primitiveRoots_nine_eq_image :
    primitiveRoots 9 ℂ =
      ((range 9).filter fun i => Nat.Coprime i 9).image fun i => zeta9 ^ i := by
  have hζ := isPrimitiveRoot_zeta9
  ext x
  simp only [mem_image, mem_filter, mem_range, mem_primitiveRoots (by norm_num : 0 < 9)]
  constructor
  · intro hx
    rw [hζ.isPrimitiveRoot_iff] at hx
    obtain ⟨i, hin, hi, H⟩ := hx
    exact ⟨i, ⟨hin, hi⟩, H⟩
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact hζ.pow_of_coprime i hi

/-- The sum of the primitive 9-th roots of unity equals `μ 9`. -/
