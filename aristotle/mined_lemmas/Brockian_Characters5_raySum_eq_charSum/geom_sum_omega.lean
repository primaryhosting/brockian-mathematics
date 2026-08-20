import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` given by `x ↦ ω ^ x`. -/

theorem geom_sum_omega : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 5 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ, ω] at h ⊢
  linear_combination h

/-- Orthogonality of the characters of `ZMod 5`. -/
