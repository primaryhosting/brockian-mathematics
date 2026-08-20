import Mathlib

/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Polynomial

namespace Math

/-- **Weierstrass approximation theorem.**

Polynomials are dense in `C([a,b], ℝ)` for the sup norm:

* the set of continuous functions on `[a,b]` arising as restrictions of real polynomials is
  a dense subset of `C(Set.Icc a b, ℝ)` (whose norm is the sup norm), and
* equivalently, every continuous `f : C([a,b], ℝ)` is within any `ε > 0`, in sup norm,
  of the restriction of some polynomial `p : ℝ[X]`.
-/
theorem weierstrass_approx (a b : ℝ) :
    Dense (Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)) ∧
      ∀ (f : C(Set.Icc a b, ℝ)) (ε : ℝ), 0 < ε →
        ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε := by
  have hclosure := polynomialFunctions_closure_eq_top a b
  constructor
  · have hcoe : (Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)) =
        (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
      rw [polynomialFunctions_coe]; rfl
    rw [hcoe, dense_iff_closure_eq]
    have h : (((polynomialFunctions (Set.Icc a b)).topologicalClosure :
        Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ)) =
        ((⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ)) := by
      rw [hclosure]
    simpa [Subalgebra.topologicalClosure_coe] using h
  · intro f ε hε
    exact exists_polynomial_near_continuousMap a b f ε hε

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

