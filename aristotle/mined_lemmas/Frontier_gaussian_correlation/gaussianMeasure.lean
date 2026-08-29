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

open MeasureTheory ProbabilityTheory

/-- The standard (centered, isotropic) Gaussian measure on `ℝ ^ n`, realized as the product of
`n` copies of the standard Gaussian measure on `ℝ`. -/

noncomputable def gaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure; infer_instance

/-- `GaussianCorrelationHolds n` is the Gaussian correlation inequality (Royen's theorem) in
dimension `n`: for any two origin-symmetric convex sets `K`, `L` in `ℝ ^ n`, the standard
Gaussian measure of the intersection is at least the product of the measures. The full
Gaussian correlation inequality is the statement `∀ n, GaussianCorrelationHolds n`. -/
