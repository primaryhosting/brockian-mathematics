import Mathlib
/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: verified (builds; axioms: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Polynomial

namespace Math

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)`, whose topology is that of the sup norm.

The key input is Mathlib's `polynomialFunctions_closure_eq_top`. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
  rw [dense_iff_closure_eq]
  have h := polynomialFunctions_closure_eq_top a b
  have h' : (((polynomialFunctions (Set.Icc a b)).topologicalClosure :
      Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ)) =
      (Set.univ : Set C(Set.Icc a b, ℝ)) := by
    rw [h]; rfl
  simpa [Subalgebra.topologicalClosure_coe] using h'

/-- Explicit sup-norm form of the Weierstrass approximation theorem: every continuous
real-valued function on `[a,b]` is uniformly approximated on `[a,b]` by a polynomial to
within any prescribed `ε > 0`. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (ε : ℝ) (hε : 0 < ε) : ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

end Math

import Mathlib

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

