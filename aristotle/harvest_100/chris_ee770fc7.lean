/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
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

/-- **Lagrange's Mean Value Theorem.**  If `a < b`, `f` is continuous on `[a, b]` and
differentiable at every point of `(a, b)`, then there is `c ∈ (a, b)` with
`deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  refine exists_hasDerivAt_eq_slope f (deriv f) hab hfc ?_
  intro x hx
  exact (hfd x hx).hasDerivAt

/-- Variant of the Mean Value Theorem for a function differentiable on all of `ℝ`
(in particular on `[a, b]`), phrased with an arbitrary derivative function `f'`. -/
theorem mean_value' (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  refine exists_hasDerivAt_eq_slope f f' hab ?_ ?_
  · exact fun x hx => ((hf x hx).continuousAt).continuousWithinAt
  · exact fun x hx => hf x (Set.mem_Icc_of_Ioo hx)

end Math

