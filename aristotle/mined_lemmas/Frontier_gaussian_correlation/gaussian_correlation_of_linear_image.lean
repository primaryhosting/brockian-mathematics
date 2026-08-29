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

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard (centered, identity–covariance) Gaussian measure on `Fin n → ℝ`:
the `n`-fold product of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem gaussian_correlation_of_linear_image {n m : ℕ}
    (h : GaussianCorrelationInequality n)
    (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hT : Measurable T)
    (K L : Set (Fin m → ℝ)) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : IsSymmetric K) (hLs : IsSymmetric L)
    (hKm : MeasurableSet K) (hLm : MeasurableSet L) :
    ((stdGaussian n).map T) K * ((stdGaussian n).map T) L
      ≤ ((stdGaussian n).map T) (K ∩ L) := by
  rw [Measure.map_apply hT hKm, Measure.map_apply hT hLm,
    Measure.map_apply hT (hKm.inter hLm), Set.preimage_inter]
  refine h _ _ (hK.linear_preimage T) (hL.linear_preimage T) ?_ ?_ (hT hKm) (hT hLm)
  · intro x hx
    have : T (-x) = -T x := map_neg T x
    simp only [Set.mem_preimage, this]
    exact hKs _ hx
  · intro x hx
    have : T (-x) = -T x := map_neg T x
    simp only [Set.mem_preimage, this]
    exact hLs _ hx

end Frontier

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

