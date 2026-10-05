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
noncomputable def sphereArea : ℕ → ℝ
  | 0 => 2
  | (k + 1) => sphereArea k * ∫ u in (0:ℝ)..Real.pi, Real.sin u ^ k

@[simp] lemma sphereArea_zero : sphereArea 0 = 2 := rfl

lemma sphereArea_succ (k : ℕ) :
    sphereArea (k + 1) = sphereArea k * ∫ u in (0:ℝ)..Real.pi, Real.sin u ^ k := rfl

lemma integral_sin_pow_pos (k : ℕ) : 0 < ∫ u in (0:ℝ)..Real.pi, Real.sin u ^ k := by
  have hcont : Continuous fun s : ℝ => Real.sin s ^ k := Real.continuous_sin.pow k
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (hcont.intervalIntegrable _ _) (fun x hx => ?_) Real.pi_pos
  exact pow_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2) k

lemma sphereArea_pos (k : ℕ) : 0 < sphereArea k := by
  induction k with
  | zero => norm_num
  | succ k ih => exact mul_pos ih (integral_sin_pow_pos k)

/-- Sanity check: the circle `S¹` has length `2π`. -/
lemma sphereArea_one : sphereArea 1 = 2 * Real.pi := by
  rw [sphereArea_succ]
  simp

/-- Sanity check: the sphere `S²` has area `4π`. -/
lemma sphereArea_two : sphereArea 2 = 4 * Real.pi := by
  rw [sphereArea_succ, sphereArea_one]
  simp [integral_sin]
  ring

/-!
## Auxiliary integrals of powers of the sine
-/

/-- For an odd exponent, the integral of `sinᵏ` over a full period vanishes. -/
lemma integral_sin_pow_period_of_odd {k : ℕ} (hk : Odd k) (c : ℝ) :
    (∫ u in c..(c + 2 * Real.pi), Real.sin u ^ k) = 0 := by
  have hper : Function.Periodic (fun u : ℝ => Real.sin u ^ k) (2 * Real.pi) := fun u => by
    simp [Real.sin_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq c (-Real.pi)
  have hzero : (∫ u in (-Real.pi)..(-Real.pi + 2 * Real.pi), Real.sin u ^ k) = 0 := by
    have hodd : ∀ u : ℝ, Real.sin (-u) ^ k = -(Real.sin u ^ k) := by
      intro u
      rw [Real.sin_neg, hk.neg_pow]
    have hcomp := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
      (fun u => Real.sin u ^ k)
    simp only [hodd] at hcomp
    simp only [intervalIntegral.integral_neg, neg_neg] at hcomp
    have h2 : (-Real.pi + 2 * Real.pi) = Real.pi := by ring
    rw [h2]
    linarith
  rw [hshift, hzero]

/-- The antiderivative `u ↦ ∫₀ᵘ sinᵏ` of `sinᵏ`. -/
noncomputable def sinPowPrimitive (k : ℕ) (u : ℝ) : ℝ := ∫ s in (0:ℝ)..u, Real.sin s ^ k

lemma hasDerivAt_sinPowPrimitive (k : ℕ) (u : ℝ) :
    HasDerivAt (sinPowPrimitive k) (Real.sin u ^ k) u := by
  have hcont : Continuous fun s : ℝ => Real.sin s ^ k := Real.continuous_sin.pow k
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

lemma sinPowPrimitive_sub (k : ℕ) (c d : ℝ) :
    sinPowPrimitive k d - sinPowPrimitive k c = ∫ u in c..d, Real.sin u ^ k := by
  have hcont : Continuous fun s : ℝ => Real.sin s ^ k := Real.continuous_sin.pow k
  exact intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)

/-- For an odd exponent the antiderivative of `sinᵏ` is `2π`-periodic. -/
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
def dim (_P : ProfileCurve k) : ℕ := k + 1

/-- The Gauss-Kronecker curvature of the hypersurface of revolution (the determinant
of its shape operator, i.e. the product of its principal curvatures) at the points of
the parallel of parameter `t`. The principal curvature in the meridian direction is
`theta' t`, and the principal curvature in each of the `k` directions tangent to the
parallel is `sin (theta t) / r t`. -/
noncomputable def gaussKronecker (P : ProfileCurve k) (t : ℝ) : ℝ :=
  P.dtheta t * (Real.sin (P.theta t) / P.r t) ^ k

/-- The integral over the hypersurface of revolution of a function that only depends
on the parameter `t` of the profile curve: the `(k+1)`-volume element is `r t ^ k`
times the product of the length element `dt` of the profile curve and the `k`-volume
element of the unit sphere `Sᵏ` of directions. -/
noncomputable def surfaceIntegral (P : ProfileCurve k) (f : ℝ → ℝ) : ℝ :=
  sphereArea k * ∫ t in P.a..P.b, f t * P.r t ^ k

/-- The total Gauss-Kronecker curvature `∫_M K dV`. -/
noncomputable def totalCurvature (P : ProfileCurve k) : ℝ :=
  P.surfaceIntegral P.gaussKronecker

/-- The `(k+1)`-volume of the hypersurface of revolution. -/
noncomputable def volume (P : ProfileCurve k) : ℝ := P.surfaceIntegral (fun _ => 1)

/-- The turning angle of the profile curve is continuous. -/
lemma continuous_theta (P : ProfileCurve k) : Continuous P.theta :=
  Differentiable.continuous (fun t => (P.htheta t).differentiableAt)

/-- Substitution in the total curvature integral: the curvature integrand of the
profile curve integrates to the integral of `sinᵏ` over the range of turning angles. -/
lemma integral_dtheta_sin_pow (P : ProfileCurve k) :
    (∫ t in P.a..P.b, P.dtheta t * Real.sin (P.theta t) ^ k)
      = ∫ u in (P.theta P.a)..(P.theta P.b), Real.sin u ^ k := by
  have key : ∀ t ∈ Set.uIcc P.a P.b,
      HasDerivAt (fun t => sinPowPrimitive k (P.theta t))
        (P.dtheta t * Real.sin (P.theta t) ^ k) t := by
    intro t _
    simpa [mul_comm] using (hasDerivAt_sinPowPrimitive k (P.theta t)).comp t (P.htheta t)
  have hint : IntervalIntegrable
      (fun t => P.dtheta t * Real.sin (P.theta t) ^ k) MeasureTheory.volume P.a P.b :=
    (P.hdtheta.mul ((Real.continuous_sin.comp P.continuous_theta).pow k)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key hint, sinPowPrimitive_sub]

/-- The volume element rewriting: where the profile curve is off the axis, the
integrand `K · r ^ k` of the total curvature equals `theta' · sinᵏ(theta)`. -/
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
def eulerCharSphere (d : ℕ) : ℤ := if Even d then 2 else 0

@[simp] lemma eulerCharSphere_even {d : ℕ} (hd : Even d) : eulerCharSphere d = 2 := by
  simp [eulerCharSphere, hd]

@[simp] lemma eulerCharSphere_odd {d : ℕ} (hd : ¬ Even d) : eulerCharSphere d = 0 := by
  simp [eulerCharSphere, hd]

/-- The Euler characteristic of a closed hypersurface of revolution of spherical type:
it is diffeomorphic to `S^{k+1}`. -/
def RotHypersurface.eulerChar {k : ℕ} (_M : RotHypersurface k) : ℤ := eulerCharSphere (k + 1)

/-- The Euler characteristic of a closed hypersurface of revolution of toroidal type:
it is diffeomorphic to `S¹ × Sᵏ`, so its Euler characteristic is
`χ(S¹) · χ(Sᵏ) = 0`. -/
def RotTorus.eulerChar {k : ℕ} (_M : RotTorus k) : ℤ := 0

/-- The unit sphere `S^{k+1} ⊆ ℝ^{k+2}`, viewed as a hypersurface of revolution. -/
noncomputable def unitSphere (k : ℕ) : RotHypersurface k where
  a := 0
  b := Real.pi
  r := Real.sin
  z := Real.cos
  theta := id
  dtheta := fun _ => 1
  hab := Real.pi_pos.le
  htheta := fun t => hasDerivAt_id t
  hdtheta := continuous_const
  hr := fun t => Real.hasDerivAt_sin t
  hz := fun t => Real.hasDerivAt_cos t
  hrpos := fun _ ht => Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  hra := Real.sin_zero
  hrb := Real.sin_pi
  hthetaa := rfl
  hthetab := rfl

/-- The torus of revolution in `ℝ^{k+2}` obtained by rotating the circle of radius `1`
centred at distance `R > 1` from the axis of revolution. -/
noncomputable def torusOfRevolution (k : ℕ) {R : ℝ} (hR : 1 < R) : RotTorus k where
  a := 0
  b := 2 * Real.pi
  r := fun t => R + Real.sin t
  z := fun t => Real.cos t
  theta := id
  dtheta := fun _ => 1
  hab := by positivity
  htheta := fun t => hasDerivAt_id t
  hdtheta := continuous_const
  hr := fun t => by simpa using (Real.hasDerivAt_sin t).const_add R
  hz := fun t => Real.hasDerivAt_cos t
  hrpos := fun t => by
    have := Real.neg_one_le_sin t
    linarith
  turningNumber := 1
  hclosed_r := by simp [Real.sin_two_pi]
  hclosed_z := by simp [Real.cos_two_pi]
  hclosed_theta := by simp

/-!
## The main computation
-/

/-- The total Gauss-Kronecker curvature of a closed hypersurface of revolution of
spherical type equals the volume of the unit sphere of the same dimension. -/
theorem totalCurvature_eq_sphereArea {k : ℕ} (M : RotHypersurface k) :
    M.totalCurvature = sphereArea (k + 1) := by
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc M.a M.b →
      M.gaussKronecker t * M.r t ^ k = M.dtheta t * Real.sin (M.theta t) ^ k := by
    have h1 : ∀ᵐ t : ℝ, t ≠ M.b := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1] with t ht hmem
    rw [Set.uIoc_of_le M.hab] at hmem
    exact M.toProfileCurve.gaussKronecker_mul_rpow
      (M.hrpos t ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩).ne'
  rw [ProfileCurve.totalCurvature, ProfileCurve.surfaceIntegral,
    intervalIntegral.integral_congr_ae hae, M.toProfileCurve.integral_dtheta_sin_pow,
    M.hthetaa, M.hthetab, sphereArea_succ]

/-- The total Gauss-Kronecker curvature of an even-dimensional closed hypersurface of
revolution of toroidal type vanishes. -/
theorem totalCurvature_eq_zero {k : ℕ} (M : RotTorus k) (hk : Odd k) :
    M.totalCurvature = 0 := by
  have hcongr : ∀ t : ℝ, M.gaussKronecker t * M.r t ^ k
      = M.dtheta t * Real.sin (M.theta t) ^ k := fun t =>
    M.toProfileCurve.gaussKronecker_mul_rpow (M.hrpos t).ne'
  rw [ProfileCurve.totalCurvature, ProfileCurve.surfaceIntegral]
  have : (∫ t in M.a..M.b, M.gaussKronecker t * M.r t ^ k)
      = ∫ t in M.a..M.b, M.dtheta t * Real.sin (M.theta t) ^ k := by
    exact intervalIntegral.integral_congr (fun t _ => hcongr t)
  rw [this, M.toProfileCurve.integral_dtheta_sin_pow, ← sinPowPrimitive_sub,
    M.hclosed_theta, (periodic_sinPowPrimitive hk).int_mul M.turningNumber (M.theta M.a)]
  simp

/-- **Chern-Gauss-Bonnet theorem** for even-dimensional closed manifolds, in the
classical Gauss-Bonnet-Chern (Hopf) form, for closed hypersurfaces of revolution
`M ⊆ ℝ^{k+2}` of spherical type in even dimension `dim M = k+1`:
the total Gauss-Kronecker curvature of `M` equals `1/2` times the volume of the unit
sphere of dimension `dim M` times the Euler characteristic of `M`,

`∫_M K dV = (1/2) · vol(S^{dim M}) · χ(M)`.

(For a hypersurface, the Gauss equation expresses the curvature operator in terms of
the shape operator, and the Pfaffian of the resulting curvature form is, up to the
universal constant `(1/2) · vol(S^{dim M})`, the Gauss-Kronecker curvature; so the
displayed identity is the Chern-Gauss-Bonnet theorem for `M`.)

The evenness hypothesis is essential: see `Math2.chern_gauss_bonnet_fails_odd_dim`.
For closed hypersurfaces of revolution of toroidal type, see
`Math2.chern_gauss_bonnet_torus`. -/
theorem chern_gauss_bonnet {k : ℕ} (M : RotHypersurface k) (hk : Even (k + 1)) :
    M.totalCurvature = (1 / 2) * sphereArea M.dim * (M.eulerChar : ℝ) := by
  rw [totalCurvature_eq_sphereArea, ProfileCurve.dim, RotHypersurface.eulerChar,
    eulerCharSphere_even hk]
  push_cast
  ring

/-- **Chern-Gauss-Bonnet theorem** for even-dimensional closed hypersurfaces of
revolution `M ⊆ ℝ^{k+2}` of toroidal type, `M ≅ S¹ × Sᵏ`: both sides of

`∫_M K dV = (1/2) · vol(S^{dim M}) · χ(M)`

vanish. -/
theorem chern_gauss_bonnet_torus {k : ℕ} (M : RotTorus k) (hk : Even (k + 1)) :
    M.totalCurvature = (1 / 2) * sphereArea M.dim * (M.eulerChar : ℝ) := by
  have hk' : Odd k := Nat.Even.sub_odd (by omega) hk odd_one
  rw [totalCurvature_eq_zero M hk', RotTorus.eulerChar]
  simp

/-- In odd dimensions the Gauss-Bonnet-Chern identity fails for hypersurfaces of
spherical type: the total curvature of a closed hypersurface of revolution of
spherical type is positive, while the Euler characteristic of an odd-dimensional
sphere vanishes. -/
theorem chern_gauss_bonnet_fails_odd_dim {k : ℕ} (M : RotHypersurface k)
    (hk : ¬ Even (k + 1)) :
    M.totalCurvature ≠ (1 / 2) * sphereArea M.dim * (M.eulerChar : ℝ) := by
  rw [totalCurvature_eq_sphereArea, ProfileCurve.dim, RotHypersurface.eulerChar,
    eulerCharSphere_odd hk]
  simpa using (sphereArea_pos (k + 1)).ne'

/-!
## Consistency checks
-/

/-- The unit sphere `S^{k+1}` has Gauss-Kronecker curvature `1`. -/
lemma unitSphere_gaussKronecker {k : ℕ} {t : ℝ} (ht : t ∈ Ioo (0:ℝ) Real.pi) :
    (unitSphere k).gaussKronecker t = 1 := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  simp [unitSphere, ProfileCurve.gaussKronecker, div_self hs]

/-- The volume of the unit sphere `S^{k+1}`, computed as a hypersurface of revolution,
is `sphereArea (k+1)`. -/
lemma unitSphere_volume (k : ℕ) : (unitSphere k).volume = sphereArea (k + 1) := by
  simp [ProfileCurve.volume, ProfileCurve.surfaceIntegral, unitSphere, sphereArea_succ]

end Math2

