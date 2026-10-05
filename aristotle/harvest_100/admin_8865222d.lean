/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring,
-- since Lean 4 requires `import` to precede every command, including module docs.)

import Mathlib

open Set

namespace Math

/-- **Mean value theorem.** If `a < b`, `f` is continuous on `[a, b]` and differentiable on
the open interval `(a, b)`, then there is a point `c ∈ (a, b)` with
`deriv f c = (f b - f a) / (b - a)`.

This is Mathlib's `exists_deriv_eq_slope`. -/
theorem mean_value (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

/-- Version for a globally differentiable function: if `a < b` and `f` is differentiable,
then some `c ∈ (a, b)` satisfies `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value_of_differentiable (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value f hab hf.continuous.continuousOn hf.differentiableOn

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

