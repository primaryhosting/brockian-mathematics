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

noncomputable def berryFlux (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ k₁ in (0:ℝ)..(2 * Real.pi), ∫ k₂ in (0:ℝ)..(2 * Real.pi), F k₁ k₂

/-- The Chern number of a band, i.e. the Berry flux in units of `2π`. -/
