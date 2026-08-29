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

theorem isPrimitiveRoot_neg_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    IsPrimitiveRoot (-ζ) 8 := by
  have h5 : IsPrimitiveRoot (ζ ^ 5) 8 := h.pow_of_coprime 5 (by decide)
  have hz : ζ ^ 5 = -ζ := by
    have := pow_four_eq_neg_one_of_isPrimitiveRoot_eight h
    calc ζ ^ 5 = ζ ^ 4 * ζ := by ring
    _ = -ζ := by rw [this]; ring
  rwa [hz] at h5

/-- Negation is a bijection of the set of primitive 8-th roots of unity in `ℂ`. -/
