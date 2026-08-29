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

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem gaussian_correlation_boxes (n : ℕ) (A B : Fin n → Set ℝ)
    (hAc : ∀ i, Convex ℝ (A i)) (hAs : ∀ i, ∀ x ∈ A i, -x ∈ A i)
    (hBc : ∀ i, Convex ℝ (B i)) (hBs : ∀ i, ∀ x ∈ B i, -x ∈ B i) :
    stdGaussian n (Set.univ.pi A) * stdGaussian n (Set.univ.pi B)
      ≤ stdGaussian n (Set.univ.pi A ∩ Set.univ.pi B) := by
  rw [← Set.pi_inter_distrib]
  unfold stdGaussian
  rw [Measure.pi_pi, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i _ =>
    gaussianReal_correlation (hAc i) (hAs i) (hBc i) (hBs i)

end Frontier

