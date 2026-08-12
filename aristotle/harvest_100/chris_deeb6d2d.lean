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

namespace Math

/-- **Lagrange's Mean Value Theorem**: if `f : ℝ → ℝ` is continuous on `[a, b]` and
differentiable on the interior `(a, b)` (with `a < b`), then there is a point `c ∈ (a, b)`
with `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

/-- Variant of the Mean Value Theorem phrased with differentiability on the closed
interval `[a, b]`, as in the informal statement. -/
theorem mean_value_of_differentiableOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfd : DifferentiableOn ℝ f (Set.Icc a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value hab hfd.continuousOn
    (hfd.mono Set.Ioo_subset_Icc_self)

end Math

