import Mathlib
/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-- The Berry flux of a band: the integral of the Berry curvature `F` over the
Brillouin torus `[0, 2π] × [0, 2π]`. -/

theorem berryFlux_modelCurvature : berryFlux modelCurvature = 2 * Real.pi := by
  have inner : ∀ k₁ : ℝ,
      (∫ k₂ in (0:ℝ)..(2 * Real.pi), modelCurvature k₁ k₂) = 1 := by
    intro k₁
    simp only [modelCurvature]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_cos.const_mul _),
      intervalIntegral.integral_const_mul, integral_cos]
    simp [Real.sin_two_pi]
  rw [berryFlux]
  simp [inner]

/-- The model band has Chern number one. -/
