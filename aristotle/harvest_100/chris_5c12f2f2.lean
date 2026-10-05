/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
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

namespace Math

open scoped Polynomial

/-- The set of elements of `C([a,b], ℝ)` which are restrictions of real polynomials. -/
def polySet (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)` equipped with the sup norm. -/
theorem weierstrass_approx (a b : ℝ) : Dense (polySet a b) := by
  intro f
  rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  refine ⟨p.toContinuousMapOn (Set.Icc a b), ⟨p, rfl⟩, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hp

/-- Sup-norm form of the Weierstrass approximation theorem: every continuous map on `[a,b]`
is within `ε` (in sup norm) of a polynomial. -/
theorem weierstrass_approx_norm (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

/-- Pointwise (epsilon) form of the Weierstrass approximation theorem for functions
continuous on `[a,b]`. -/
theorem weierstrass_approx_pointwise (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

end Math

