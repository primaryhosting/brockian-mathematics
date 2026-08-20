import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.BaezDuarte

/-- **Gram nonnegativity, clean self-contained case.**
For all real `a b`, the quadratic form `a^2 - 2*a*b + b^2` is nonnegative:
it is the squared distance `(a - b)^2`, the basic building block of the
Nyman–Beurling / Baez-Duarte distance, which is a sum of such squares. -/

theorem gram_nonneg_two {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u w : V) :
    0 ≤ (inner ℝ u u) - 2 * (inner ℝ u w) + (inner ℝ w w) := by
  have h : (inner ℝ u u) - 2 * (inner ℝ u w) + (inner ℝ w w) = ‖u - w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self, real_inner_comm w u]
    ring
  rw [h]
  positivity

end Riemann.BaezDuarte

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

