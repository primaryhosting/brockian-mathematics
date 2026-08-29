/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

theorem donsker_invariance_marginal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {t : ℝ} (ht : 0 ≤ t) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (donskerInterp X n t ω) ∂P) atTop
      (𝓝 (∫ ω, f (B t ω) ∂P')) := by
  have hBt : P'.map (B t) = gaussianReal 0 t.toNNReal := by
    have h := hB.gaussian_increments 0 t le_rfl ht
    simpa [hB.start_zero] using h
  have h1 : ∫ ω, f (B t ω) ∂P' = ∫ x, f x ∂(gaussianReal 0 t.toNNReal) := by
    rw [← hBt, integral_map (hB.measurable t).aemeasurable f.continuous.aestronglyMeasurable]
  rw [h1]
  exact tendsto_integral_donskerInterp hmeas hindep hlaw ht f

/-!
## Convergence of the finite-dimensional distributions

We now prove the stronger statement that all finite-dimensional distributions of the rescaled
walk converge to those of Brownian motion.  For this we use the (right-continuous) step version
of the rescaled walk, `donskerStep X n t = S_{⌊nt⌋}/√n`.
-/

/-- The rescaled random walk `t ↦ S_{⌊nt⌋}/√n`. -/
