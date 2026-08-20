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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complex Hilbert space `L²(E)` of square integrable functions on a finite-dimensional
real inner product space `E`, with respect to the Lebesgue (Haar) measure. -/
abbrev L2Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Type _ := ↥(Lp (α := E) ℂ 2 volume)

/-- Schwartz functions viewed as elements of `L²(E)`. -/

theorem memLp_multiplier_mul_of_support (n : ℕ) {u : E → ℂ} (hu : MemLp u 2 volume)
    (hsupp : ∀ ξ ∉ Metric.closedBall (0 : E) n, u ξ = 0) :
    MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume := by
  refine MemLp.of_le (hu.const_mul (((4 * π ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ)))
    (continuous_multiplier.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ξ ∈ Metric.closedBall (0 : E) n
  · have hb1 : ‖(multiplier ξ : ℂ) * u ξ‖ = multiplier ξ * ‖u ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplier_nonneg ξ)]
    have hb2 : ‖((4 * π ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ) * u ξ‖ = (4 * π ^ 2 * (n : ℝ) ^ 2) * ‖u ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * π ^ 2 * (n:ℝ) ^ 2)]
    rw [hb1, hb2]
    exact mul_le_mul_of_nonneg_right (multiplier_le_of_mem_closedBall n hξ) (norm_nonneg _)
  · simp [hsupp ξ hξ]

/-- Every `L²` function `u` such that `multiplier · u` is again in `L²` gives, via the inverse
Fourier transform, an element of the domain of the adjoint. -/
