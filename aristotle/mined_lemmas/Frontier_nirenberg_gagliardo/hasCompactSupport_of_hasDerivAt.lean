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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz for the Lebesgue integral on `ℝ`: for continuous, compactly supported
`u, v : ℝ → ℝ` we have `∫ |u| |v| ≤ √(∫ u²) * √(∫ v²)`. -/

lemma hasCompactSupport_of_hasDerivAt {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hsupp : HasCompactSupport f) : HasCompactSupport f' := by
  have hfd : f' = deriv f := funext fun t => ((hderiv t).deriv).symm
  rw [hfd]
  exact hsupp.deriv

/-- Below the (compact) support of `f`, the function vanishes: there is `a ≤ x` with `f a = 0`. -/
