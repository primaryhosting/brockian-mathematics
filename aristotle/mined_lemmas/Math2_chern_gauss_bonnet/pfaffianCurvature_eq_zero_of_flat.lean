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

theorem pfaffianCurvature_eq_zero_of_flat {n : ℕ} (hn : 0 < n)
    {R : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ}
    (hR : ∀ i j k l, R i j k l = 0) : pfaffianCurvature n R = 0 := by
  have hprod : ∀ σ τ : Equiv.Perm (Fin (2 * n)),
      ∏ i : Fin n, R (σ (idx i 0)) (σ (idx i 1)) (τ (idx i 0)) (τ (idx i 1)) = 0 := by
    intro σ τ
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) (hR _ _ _ _)
  simp [pfaffianCurvature, hprod]

/-! ## The Chern–Gauss–Bonnet theorem

We formalise the theorem in the setting of the heat-equation (McKean–Singer/Patodi–Gilkey) proof.
A `ChernGaussBonnetSetup` packages a closed even-dimensional oriented Riemannian manifold
together with the two analytic inputs of that proof:

* the *McKean–Singer formula*: for every `t > 0` the integral over `M` of the pointwise
  supertrace of the heat kernel of the Hodge Laplacian equals the Euler characteristic of `M`;
* the *local index theorem* of Patodi and Gilkey: as `t → 0⁺` that pointwise supertrace
  converges to the Pfaffian curvature density `Pf(Ω / (2π))`, together with the uniform bound
  on the supertrace for small `t` that comes from the heat-kernel asymptotics.

Mathlib currently contains neither Riemannian curvature nor de Rham cohomology nor heat kernels,
so these two inputs are taken as hypotheses; the theorem below is the resulting
Chern–Gauss–Bonnet identity

`∫_M Pf(Ω / (2π)) dvol = χ(M)`.

Concrete non-degenerate data satisfying all the hypotheses (with `χ = 2`, modelling the round
two-sphere) is exhibited in `Math2.sphereModel` below, so the hypotheses are consistent. -/

/-- Data for the heat-equation proof of the Chern–Gauss–Bonnet theorem on a closed oriented
Riemannian manifold of even dimension `2 * n`. -/
structure ChernGaussBonnetSetup where
  /-- The underlying set of points of the closed manifold `M`. -/
  Point : Type
  [measurableSpace : MeasurableSpace Point]
  /-- The Riemannian volume measure of `M`. -/
  vol : Measure Point
  /-- `M` is closed, hence of finite volume. -/
  [isFinite : IsFiniteMeasure vol]
  /-- Half the dimension of `M`; the dimension of `M` is `2 * n`. -/
  n : ℕ
  /-- The Euler characteristic `χ(M)`. -/
  euler : ℤ
  /-- The components of the Riemann curvature tensor in an oriented orthonormal frame. -/
  riemann : Point → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ
  /-- The pointwise supertrace `str k_t(x, x)` of the heat kernel of the Hodge Laplacian
  acting on differential forms. -/
  heatSupertrace : ℝ → Point → ℝ
  measurable_heatSupertrace : ∀ t : ℝ, 0 < t → AEStronglyMeasurable (heatSupertrace t) vol
  /-- McKean–Singer: the integrated supertrace of the heat kernel is the Euler characteristic. -/
  mckean_singer : ∀ t : ℝ, 0 < t → ∫ x, heatSupertrace t x ∂vol = (euler : ℝ)
  /-- The local index theorem (Patodi, Gilkey): the pointwise supertrace converges, as
  `t → 0⁺`, to the Pfaffian of the curvature. -/
  local_index : ∀ x : Point, Tendsto (fun t : ℝ => heatSupertrace t x) (𝓝[>] (0 : ℝ))
    (𝓝 (pfaffianCurvature n (riemann x)))
  /-- The supertrace is uniformly bounded for small times. -/
  uniform_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < 1 → ∀ x : Point, |heatSupertrace t x| ≤ C

attribute [instance] ChernGaussBonnetSetup.measurableSpace ChernGaussBonnetSetup.isFinite

/-- The Euler form density `Pf(Ω / (2π))` of a Chern–Gauss–Bonnet setup. -/
