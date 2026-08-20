import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
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

/-- The "Mexican hat" scalar potential of the abelian Higgs model, written as a
function of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma deriv2_higgsPotential (lam v : ℝ) :
    deriv (deriv (higgsPotential lam v)) = fun r => 4 * lam * (3 * r ^ 2 - v ^ 2) := by
  funext r
  rw [deriv_higgsPotential]
  have h : HasDerivAt (fun r : ℝ => 4 * lam * r * (r ^ 2 - v ^ 2))
      (4 * lam * (3 * r ^ 2 - v ^ 2)) r := by
    have h1 : HasDerivAt (fun x : ℝ => 4 * lam * x) (4 * lam) r := by
      simpa using (hasDerivAt_id r).const_mul (4 * lam)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 - v ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).sub_const (v ^ 2)
    have := h1.mul h2
    refine this.congr_deriv ?_
    ring
  exact h.deriv

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

For a `U(1)` gauge coupling `g > 0`, quartic coupling `lam > 0` and symmetry breaking
scale `v > 0`:

* the Mexican-hat potential `V(r) = lam (r² - v²)²` is minimized at the broken vacuum
  `r = v`, where it vanishes, and the symmetric point `r = 0` is *not* a minimum
  (`V(0) > V(v)`), i.e. the symmetry is spontaneously broken;
* `r = v` is a genuine stationary point with positive curvature, the physical Higgs
  mass squared being `V''(v) = 8 lam v² > 0`;
* expanding the covariant kinetic term about the vacuum produces the quadratic gauge
  term `g² v² A²`, i.e. a mass squared `m_A² = g² v² > 0` with `m_A = g v > 0`,
  whereas about the symmetric point `r = 0` the gauge field stays massless;
* in the complex-field formulation, `V(φ) = lam (|φ|² - v²)²` is nonnegative and vanishes
  exactly on the vacuum circle `|φ| = v` (a degenerate vacuum manifold, the origin of the
  Goldstone mode), both `V` and the covariant kinetic term `|Dφ|²`, `Dφ = ∂φ - i g A φ`,
  are invariant under global `U(1)` rotations `φ ↦ e^{iθ} φ`, and evaluating `|Dφ|²` on the
  constant vacuum `φ = v` produces exactly the gauge mass term `m_A² A²`, while at `φ = 0`
  it vanishes. -/
