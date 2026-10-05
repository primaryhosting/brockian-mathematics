import Mathlib
/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory intervalIntegral Set

/-!
## Scope of this formalization

The Chern-Gauss-Bonnet theorem states that for a closed oriented Riemannian manifold
`M` of even dimension `d`, the integral over `M` of the Euler form built from the
curvature (the Pfaffian of the curvature two-form, suitably normalized) equals the
Euler characteristic of `M`.

Mathlib currently contains none of the ingredients of the general smooth statement:
there is no curvature tensor of a Riemannian metric, no Pfaffian, no integration of
differential forms over manifolds, and no Euler characteristic of a manifold. What is
formalized here, from scratch and in every detail, is the classical
Gauss-Bonnet-Chern (Hopf) form of the theorem,

`∫_M K dV = (1/2) · vol(S^d) · χ(M)`,

where `K` is the Gauss-Kronecker curvature (the determinant of the shape operator),
for the closed hypersurfaces of revolution `M ⊆ ℝ^{d+1}` of even dimension `d`. For a
hypersurface, the Gauss equation expresses the curvature operator in terms of the
shape operator, and the Pfaffian of the resulting curvature form is exactly
`K` divided by the universal constant `(1/2) · vol(S^d)`, so this is the
Chern-Gauss-Bonnet theorem for these manifolds. Both topological types that occur are
treated: the spherical one, `M ≅ S^d` with `χ(M) = 2` (`Math2.chern_gauss_bonnet`),
and the toroidal one, `M ≅ S¹ × S^{d-1}` with `χ(M) = 0`
(`Math2.chern_gauss_bonnet_torus`). That the dimension is even is essential, see
`Math2.chern_gauss_bonnet_fails_odd_dim`.

## The volume of the unit spheres

`sphereArea k` is the `k`-dimensional volume of the unit sphere `Sᵏ ⊆ ℝ^{k+1}`.
It is defined by the classical recursion obtained by slicing `S^{k+1}` into the
parallels `{(sin t · ω, cos t) | ω ∈ Sᵏ}`, `t ∈ [0, π]`, whose `k`-volume is
`sin t ^ k · sphereArea k`; the base case is `S⁰ = {-1, 1}`, of `0`-volume `2`.
-/

/-- `sphereArea k` is the `k`-dimensional volume of the unit sphere `Sᵏ ⊆ ℝ^{k+1}`. -/

lemma periodic_sinPowPrimitive {k : ℕ} (hk : Odd k) :
    Function.Periodic (sinPowPrimitive k) (2 * Real.pi) := by
  intro u
  have := sinPowPrimitive_sub k u (u + 2 * Real.pi)
  rw [integral_sin_pow_period_of_odd hk u] at this
  linarith

/-!
## Closed hypersurfaces of revolution

A hypersurface of revolution `M ⊆ ℝ^{k+2}` of dimension `k+1` is swept out by
rotating a profile curve `t ↦ (r t, z t)`, `t ∈ [a,b]`, of unit speed, around the
`z`-axis:

`M = { (r t · ω, z t) | t ∈ [a,b], ω ∈ Sᵏ ⊆ ℝ^{k+1} }`.

Unit speed of the profile curve is encoded through its turning angle `theta`:
`r' = cos theta` and `z' = -sin theta`, which is the data recorded by
`Math2.ProfileCurve`.

Two families of *closed* such hypersurfaces are considered below.

* Spherical type (`Math2.RotHypersurface`): the profile curve meets the axis exactly
  at its two endpoints (`r a = r b = 0`, `r > 0` in between) and does so
  orthogonally, `theta a = 0` and `theta b = π`. Then `M` is a closed hypersurface
  diffeomorphic to the sphere `S^{k+1}`, of Euler characteristic `2` when `k+1` is
  even. The unit sphere is of this type, see `Math2.unitSphere`.

* Toroidal type (`Math2.RotTorus`): the profile curve stays off the axis
  (`r > 0` everywhere) and closes up smoothly, its turning angle increasing by
  `2π` times its turning number. Then `M` is a closed hypersurface diffeomorphic to
  `S¹ × Sᵏ`, of Euler characteristic `0`. The standard torus of revolution in `ℝ³`
  is of this type, see `Math2.torusOfRevolution`.
-/

/-- The profile curve of a hypersurface of revolution `M ⊆ ℝ^{k+2}` of dimension
`k+1`: a unit-speed plane curve `t ↦ (r t, z t)` with turning angle `theta`, so that
`r' = cos theta` and `z' = -sin theta`. -/
structure ProfileCurve (k : ℕ) where
  /-- Left endpoint of the parameter interval of the profile curve. -/
  a : ℝ
  /-- Right endpoint of the parameter interval of the profile curve. -/
  b : ℝ
  /-- The distance of the profile curve to the axis of revolution. -/
  r : ℝ → ℝ
  /-- The height of the profile curve along the axis of revolution. -/
  z : ℝ → ℝ
  /-- The turning angle of the profile curve. -/
  theta : ℝ → ℝ
  /-- The derivative of the turning angle (the curvature of the profile curve). -/
  dtheta : ℝ → ℝ
  hab : a ≤ b
  htheta : ∀ t : ℝ, HasDerivAt theta (dtheta t) t
  hdtheta : Continuous dtheta
  /-- Unit-speed parametrization, first component. -/
  hr : ∀ t : ℝ, HasDerivAt r (Real.cos (theta t)) t
  /-- Unit-speed parametrization, second component. -/
  hz : ∀ t : ℝ, HasDerivAt z (-Real.sin (theta t)) t

namespace ProfileCurve

variable {k : ℕ}

/-- The dimension of the hypersurface of revolution `M ⊆ ℝ^{k+2}` swept out by the
profile curve. -/
