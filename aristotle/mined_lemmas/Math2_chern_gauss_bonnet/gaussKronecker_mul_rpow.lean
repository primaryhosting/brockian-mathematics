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

lemma gaussKronecker_mul_rpow (P : ProfileCurve k) {t : ℝ} (ht : P.r t ≠ 0) :
    P.gaussKronecker t * P.r t ^ k = P.dtheta t * Real.sin (P.theta t) ^ k := by
  rw [gaussKronecker, div_pow, mul_assoc, div_mul_cancel₀]
  exact pow_ne_zero k ht

end ProfileCurve

/-- A closed hypersurface of revolution of dimension `k+1` in `ℝ^{k+2}` of spherical
type: the profile curve runs from a pole to a pole, meeting the axis of revolution
orthogonally at its two endpoints and staying off it in between. Such an `M` is
diffeomorphic to the sphere `S^{k+1}`. -/
structure RotHypersurface (k : ℕ) extends ProfileCurve k where
  /-- The profile curve stays off the axis in the interior. -/
  hrpos : ∀ t ∈ Ioo toProfileCurve.a toProfileCurve.b, 0 < toProfileCurve.r t
  /-- The profile curve meets the axis at the left endpoint (south pole). -/
  hra : toProfileCurve.r toProfileCurve.a = 0
  /-- The profile curve meets the axis at the right endpoint (north pole). -/
  hrb : toProfileCurve.r toProfileCurve.b = 0
  /-- The profile curve leaves the axis orthogonally at the south pole. -/
  hthetaa : toProfileCurve.theta toProfileCurve.a = 0
  /-- The profile curve returns to the axis orthogonally at the north pole. -/
  hthetab : toProfileCurve.theta toProfileCurve.b = Real.pi

/-- A closed hypersurface of revolution of dimension `k+1` in `ℝ^{k+2}` of toroidal
type: the profile curve is a closed curve staying off the axis of revolution, with
turning number `turningNumber`. Such an `M` is diffeomorphic to `S¹ × Sᵏ`. -/
structure RotTorus (k : ℕ) extends ProfileCurve k where
  /-- The profile curve stays off the axis of revolution. -/
  hrpos : ∀ t : ℝ, 0 < toProfileCurve.r t
  /-- The turning number of the closed profile curve. -/
  turningNumber : ℤ
  /-- The profile curve closes up: same distance to the axis. -/
  hclosed_r : toProfileCurve.r toProfileCurve.b = toProfileCurve.r toProfileCurve.a
  /-- The profile curve closes up: same height. -/
  hclosed_z : toProfileCurve.z toProfileCurve.b = toProfileCurve.z toProfileCurve.a
  /-- The profile curve closes up smoothly: the turning angle increases by `2π` times
  the turning number. -/
  hclosed_theta : toProfileCurve.theta toProfileCurve.b
      = toProfileCurve.theta toProfileCurve.a + (turningNumber : ℝ) * (2 * Real.pi)

/-- The Euler characteristic of a sphere `Sᵈ`: it is `2` in even dimensions and `0` in
odd dimensions. -/
