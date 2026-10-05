import Mathlib
/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

The Willmore conjecture, proved by Marques and Neves (2014, Fields Medal work of
A. Neves' collaborator F. C. Marques / awarded context), asserts that every immersed
torus in `ℝ³` has Willmore energy `∫ H² dA ≥ 2π²`, with equality exactly for the
Clifford torus (and its images under conformal transformations of `S³`).

The file below formalizes and *proves* the classical base case, due to T. J. Willmore
(1965): the conjecture holds for tori of revolution, i.e. for the surfaces obtained by
revolving a circle of radius `r` about an axis at distance `R > r` in its plane.  For
these surfaces everything (mean curvature, area element, hence the Willmore energy) is
completely explicit, and we compute the energy in closed form, minimize it, and identify
the unique minimizer as the ratio `R = √2 · r` — the "Clifford" torus of revolution.
-/

/-- The mean curvature `H = (k₁ + k₂)/2` of the torus of revolution with tube radius `r`
and center-circle radius `R`, at the tube-angle `u`.  Here `k₁ = 1/r` and
`k₂ = cos u / (R + r cos u)`. -/

theorem torus_meanCurvature_eq {R r : ℝ} (hr : 0 < r) (u v : ℝ) (hA : 0 < R + r * Real.cos u) :
    (dot3 (torusXu r u v) (torusXu r u v) * dot3 (torusXvv R r u v) (torusNormal u v)
        - 2 * dot3 (torusXu r u v) (torusXv R r u v) * dot3 (torusXuv r u v) (torusNormal u v)
        + dot3 (torusXv R r u v) (torusXv R r u v) * dot3 (torusXuu r u v) (torusNormal u v))
      / (2 * (dot3 (torusXu r u v) (torusXu r u v) * dot3 (torusXv R r u v) (torusXv R r u v)
        - dot3 (torusXu r u v) (torusXv R r u v) ^ 2))
      = -torusMeanCurvature R r u := by
  rw [torus_E_eq, torus_G_eq, torus_F_eq, torus_L_eq, torus_M_eq, torus_N_eq, torusMeanCurvature]
  have h1 : r ≠ 0 := ne_of_gt hr
  have h2 : R + r * Real.cos u ≠ 0 := ne_of_gt hA
  field_simp
  ring

/-! ## The basic trigonometric integral -/

/-- `∫₀^{2π} du / (a + cos u) = 2π / √(a² - 1)` for `a > 1`. -/
