import Mathlib
/-!
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Set

/-- **Intermediate value theorem.** A real-valued function that is continuous on the
closed interval `[a, b]` (with `a ≤ b`) attains every value `y` lying between `f a`
and `f b`.  Here "between" is expressed by `y ∈ Set.uIcc (f a) (f b)`, the closed
interval with endpoints `f a` and `f b` in either order, so no monotonicity
assumption is needed.

The proof is a direct application of Mathlib's `intermediate_value_uIcc`. -/

theorem ivt_of_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {y : ℝ} (hy₁ : f a ≤ y) (hy₂ : y ≤ f b) :
    ∃ c ∈ Icc a b, f c = y :=
  ivt hab hf (mem_uIcc_of_le hy₁ hy₂)

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

