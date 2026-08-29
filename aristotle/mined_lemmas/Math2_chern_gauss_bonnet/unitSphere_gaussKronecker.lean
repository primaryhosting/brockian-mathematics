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

lemma unitSphere_gaussKronecker {k : ℕ} {t : ℝ} (ht : t ∈ Ioo (0:ℝ) Real.pi) :
    (unitSphere k).gaussKronecker t = 1 := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  simp [unitSphere, ProfileCurve.gaussKronecker, div_self hs]

/-- The volume of the unit sphere `S^{k+1}`, computed as a hypersurface of revolution,
is `sphereArea (k+1)`. -/
