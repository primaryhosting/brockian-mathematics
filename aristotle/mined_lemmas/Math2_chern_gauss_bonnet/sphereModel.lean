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

noncomputable def sphereModel : ChernGaussBonnetSetup where
  Point := Unit
  measurableSpace := ⊤
  vol := ENNReal.ofReal (4 * π) • Measure.dirac ()
  isFinite := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  n := 1
  euler := 2
  riemann := fun _ => surfaceCurvature 1
  heatSupertrace := fun _ _ => 1 / (2 * π)
  measurable_heatSupertrace := fun _ _ => aestronglyMeasurable_const
  mckean_singer := by
    intro t _
    have hpi : π ≠ 0 := Real.pi_ne_zero
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 4 * π), smul_eq_mul]
    field_simp
    ring
  local_index := by
    intro x
    rw [pfaffianCurvature_surface 1]
    exact tendsto_const_nhds
  uniform_bound := ⟨|1 / (2 * π)|, fun _ _ _ _ => le_refl _⟩

/-- Chern–Gauss–Bonnet for the two-sphere model: the total Euler form is `2 = χ(S²)`. -/
