/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open MeasureTheory Filter Topology

namespace Math2

/-! ## The Pfaffian of the curvature (the Euler form density)

On a closed oriented Riemannian manifold `M` of even dimension `2 * n`, the Euler form is
`Pf(Ω / (2π))`, where `Ω` is the curvature two-form of the Levi-Civita connection written in a
local oriented orthonormal frame.  Expanding the Pfaffian and the wedge products in that frame,
`Pf(Ω / (2π))` is the multiple

`e(x) = 1 / ((8π)^n * n!) * ∑_{σ, τ ∈ S_{2n}} sgn σ * sgn τ *
          ∏_{i < n} R_{σ(2i) σ(2i+1) τ(2i) τ(2i+1)}(x)`

of the Riemannian volume form, where `R` denotes the components of the Riemann curvature tensor
in that frame.  We take this scalar density as the (frame-independent) definition of the
integrand of the Chern–Gauss–Bonnet theorem. -/

/-- The index `2 * i + j` of `Fin (2 * n)`, used to split `Fin (2 * n)` into `n` consecutive
pairs. -/

theorem gauss_bonnet_surface {M : Type} [MeasurableSpace M] (vol : Measure M)
    [IsFiniteMeasure vol] (euler : ℤ) (K : M → ℝ) (heatSupertrace : ℝ → M → ℝ)
    (measurable_heatSupertrace : ∀ t : ℝ, 0 < t → AEStronglyMeasurable (heatSupertrace t) vol)
    (mckean_singer : ∀ t : ℝ, 0 < t → ∫ x, heatSupertrace t x ∂vol = (euler : ℝ))
    (local_index : ∀ x : M, Tendsto (fun t : ℝ => heatSupertrace t x) (𝓝[>] (0 : ℝ))
      (𝓝 (pfaffianCurvature 1 (surfaceCurvature (K x)))))
    (uniform_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < 1 → ∀ x : M, |heatSupertrace t x| ≤ C) :
    ∫ x, K x ∂vol = 2 * π * (euler : ℝ) := by
  classical
  let D : ChernGaussBonnetSetup :=
    { Point := M, measurableSpace := ‹_›, vol := vol, isFinite := ‹_›, n := 1, euler := euler
      riemann := fun x => surfaceCurvature (K x)
      heatSupertrace := heatSupertrace
      measurable_heatSupertrace := measurable_heatSupertrace
      mckean_singer := mckean_singer
      local_index := local_index
      uniform_bound := uniform_bound }
  have h := chern_gauss_bonnet D
  have hform : ∀ x : M, D.eulerForm x = K x / (2 * π) := by
    intro x
    simpa [ChernGaussBonnetSetup.eulerForm, D] using pfaffianCurvature_surface (K x)
  rw [show (∫ x, D.eulerForm x ∂D.vol) = ∫ x, K x / (2 * π) ∂vol from
    integral_congr_ae (Eventually.of_forall hform)] at h
  rw [integral_div] at h
  field_simp at h
  linarith [h]

/-- A closed flat Riemannian manifold of positive even dimension has vanishing Euler
characteristic. -/
