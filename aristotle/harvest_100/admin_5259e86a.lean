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

Polynomials are dense in `C([a,b], ℝ)` under the sup norm.
-/

namespace Math

open Polynomial

/-- The set of continuous functions on `[a, b]` that are restrictions of real polynomials. -/
def polyRestrictions (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)`, where the topology on `C([a,b], ℝ)` is the one induced by the sup norm. -/
theorem weierstrass_approx (a b : ℝ) : Dense (Math.polyRestrictions a b) := by
  have h : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
    polynomialFunctions_closure_eq_top a b
  have hset : ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) = Math.polyRestrictions a b := by
    rw [polynomialFunctions_coe]
    rfl
  intro f
  have hmem : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
    rw [h]; trivial
  have : f ∈ closure ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := hmem
  rwa [hset] at this

/-- Sup-norm form of the Weierstrass approximation theorem: every continuous function on
`[a, b]` is uniformly approximated to within any `ε > 0` by a polynomial. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) : ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
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

