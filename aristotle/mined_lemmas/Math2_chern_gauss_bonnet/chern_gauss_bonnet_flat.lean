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

theorem chern_gauss_bonnet_flat (D : ChernGaussBonnetSetup) (hn : 0 < D.n)
    (hflat : ∀ x i j k l, D.riemann x i j k l = 0) : D.euler = 0 := by
  have h := chern_gauss_bonnet D
  have hzero : ∀ x : D.Point, D.eulerForm x = 0 := fun x =>
    pfaffianCurvature_eq_zero_of_flat hn (hflat x)
  simp only [ChernGaussBonnetSetup.eulerForm] at h hzero
  rw [integral_congr_ae (Eventually.of_forall hzero), integral_zero] at h
  exact_mod_cast h.symm

/-! ## Consistency: a model with nonzero Euler characteristic

The following data satisfies all the hypotheses of `ChernGaussBonnetSetup` with Euler
characteristic `2`, total volume `4π` and constant Gauss curvature `1`, i.e. it reproduces the
numerical content of Gauss–Bonnet for the round two-sphere.  In particular the hypotheses of
`Math2.chern_gauss_bonnet` are consistent and do not force the Euler characteristic to
vanish. -/

/-- A model with the numerical data of the round two-sphere: volume `4π`, Gauss curvature `1`,
Euler characteristic `2`. -/
