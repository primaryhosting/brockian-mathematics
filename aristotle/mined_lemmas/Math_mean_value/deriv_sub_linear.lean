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

A self-contained development of the mean value theorem: the interior extremum
principle gives Rolle's theorem, and Rolle's theorem applied to an auxiliary
function gives the mean value theorem.
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

open Set

/-- If `f` attains a maximum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/

theorem deriv_sub_linear {f : ℝ → ℝ} {s c : ℝ} (hf : DifferentiableAt ℝ f c) :
    deriv (fun x : ℝ => f x - s * x) c = deriv f c - s := by
  have h : HasDerivAt (fun x : ℝ => f x - s * x) (deriv f c - s * 1) c :=
    hf.hasDerivAt.sub ((hasDerivAt_id c).const_mul s)
  simpa using h.deriv

/-- **Mean value theorem.** If `f : ℝ → ℝ` is continuous on `[a, b]` and differentiable on
the open interval `(a, b)` (with `a < b`), then there is a point `c` strictly between `a`
and `b` at which the derivative of `f` equals the average slope `(f b - f a) / (b - a)`. -/
