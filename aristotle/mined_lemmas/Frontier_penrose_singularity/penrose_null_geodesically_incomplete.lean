import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

theorem penrose_null_geodesically_incomplete (theta dtheta : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt theta (dtheta t) t)
    (hray : ∀ t ∈ Set.Ici (0 : ℝ), dtheta t ≤ -(theta t) ^ 2 / 2)
    (htrap : theta 0 < 0) : False := by
  set L : ℝ := -2 / theta 0 + 1 with hLdef
  have hsub : Set.Ico (0 : ℝ) L ⊆ Set.Ici (0 : ℝ) := fun x hx => hx.1
  let C : NullCongruence L :=
    { theta := theta
      dtheta := dtheta
      hasDerivAt := fun t ht => hderiv t (hsub ht)
      raychaudhuri := fun t ht => hray t (hsub ht) }
  have h := penrose_singularity C htrap
  simp only [C, hLdef] at h
  linarith

/-!
## A second, more geometric formulation: focal points of the transverse Jacobi field

Instead of the expansion one may follow the transverse *area radius* `rho` of the
congruence (the square root of the cross-sectional area element, i.e. the relevant
Jacobi field along the null geodesics), related to the expansion by `theta = 2 rho' / rho`.
In these variables the Raychaudhuri equation becomes the Jacobi equation

  `rho'' = -(shear ^ 2 + Ric (k, k) / 2) * rho`,

so that the null energy condition says exactly `rho'' ≤ 0` as long as `rho > 0`.  A
*trapped* surface means the congruence is initially contracting, `rho' 0 < 0`, and the
congruence is regular (no focal point yet) exactly while `rho > 0`.
-/

/-- Transverse Jacobi (area-radius) data of the null geodesic congruence orthogonal to a
closed spacelike surface, on the affine parameter range `[0, L)` on which the congruence
is still regular (`rho > 0`, i.e. no focal point has been reached).

The null energy condition enters through the Jacobi equation as the concavity
condition `rho'' ≤ 0`. -/
structure NullJacobi (L : ℝ) where
  /-- Transverse area radius of the congruence. -/
  rho : ℝ → ℝ
  /-- Its first derivative in the affine parameter. -/
  drho : ℝ → ℝ
  /-- Its second derivative in the affine parameter. -/
  ddrho : ℝ → ℝ
  /-- `drho` is the derivative of `rho`. -/
  hasDerivAt_rho : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt rho (drho t) t
  /-- `ddrho` is the derivative of `drho`. -/
  hasDerivAt_drho : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt drho (ddrho t) t
  /-- No focal point has been reached on `[0, L)`. -/
  rho_pos : ∀ t ∈ Set.Ico (0 : ℝ) L, 0 < rho t
  /-- The Jacobi equation together with the null energy condition: `rho'' ≤ 0`. -/
  jacobi_nec : ∀ t ∈ Set.Ico (0 : ℝ) L, ddrho t ≤ 0

/-- The expansion `theta = 2 rho' / rho` of a transverse Jacobi field satisfies the
Raychaudhuri inequality, so it defines a `NullCongruence`. -/
