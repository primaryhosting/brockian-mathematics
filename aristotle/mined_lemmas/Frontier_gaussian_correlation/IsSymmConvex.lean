import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

namespace Frontier

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

def IsSymmConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  Convex ℝ K ∧ ∀ x ∈ K, -x ∈ K

/-- The Gaussian correlation inequality (Royen's theorem) for the space `E`:
for every centered Gaussian measure `μ` on `E` (centered being expressed as the invariance
`μ.map (fun x ↦ -x) = μ`) and all symmetric convex measurable sets `K` and `L`, one has
`μ K * μ L ≤ μ (K ∩ L)`. -/
