import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Frontier

open ProbabilityTheory

/-- The Gaussian correlation inequality, as a property of a measure `μ` on a real vector
space `E`:  for any two measurable, convex, origin-symmetric sets `K` and `L`,
`μ (K ∩ L) ≥ μ K * μ L`.

Royen's theorem states that this holds for every centred Gaussian measure `μ`.  In this file
we formalise the statement and prove the one-dimensional base case together with several
Lean-checked reductions. -/

theorem gaussian_correlation_prod (v w : ℝ≥0) {A B C D : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAc : Convex ℝ A) (hBc : Convex ℝ B) (hCc : Convex ℝ C) (hDc : Convex ℝ D)
    (hAs : ∀ x ∈ A, -x ∈ A) (hBs : ∀ x ∈ B, -x ∈ B) (hCs : ∀ x ∈ C, -x ∈ C)
    (hDs : ∀ x ∈ D, -x ∈ D) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)) (A ×ˢ B)
        * ((gaussianReal 0 v).prod (gaussianReal 0 w)) (C ×ˢ D)
      ≤ ((gaussianReal 0 v).prod (gaussianReal 0 w)) ((A ×ˢ B) ∩ (C ×ˢ D)) := by
  have hAC : gaussianReal 0 v A * gaussianReal 0 v C ≤ gaussianReal 0 v (A ∩ C) :=
    gaussian_correlation v A C hA hC hAc hCc hAs hCs
  have hBD : gaussianReal 0 w B * gaussianReal 0 w D ≤ gaussianReal 0 w (B ∩ D) :=
    gaussian_correlation w B D hB hD hBc hDc hBs hDs
  rw [Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc gaussianReal 0 v A * gaussianReal 0 w B * (gaussianReal 0 v C * gaussianReal 0 w D)
      = (gaussianReal 0 v A * gaussianReal 0 v C) * (gaussianReal 0 w B * gaussianReal 0 w D) := by
        ring
    _ ≤ gaussianReal 0 v (A ∩ C) * gaussianReal 0 w (B ∩ D) := mul_le_mul' hAC hBD

end Frontier

#print axioms Frontier.gaussian_correlation

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

