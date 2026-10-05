/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Polynomial

namespace Math

/-- The set of polynomial functions on `[a, b]`, viewed inside the space `C([a,b], ℝ)` of
continuous real-valued functions on `[a, b]` (a normed space under the sup norm). -/
def polyFuncs (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  {g | ∃ p : ℝ[X], ∀ x : Set.Icc a b, g x = p.eval (x : ℝ)}

theorem polyFuncs_eq_coe (a b : ℝ) :
    polyFuncs a b = (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
  rw [polynomialFunctions_coe]
  ext g
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, by ext x; simpa using (hp x).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, by intro x; rfl⟩

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in the space
`C([a, b], ℝ)` of continuous real-valued functions on a closed interval, equipped with the
sup norm. -/
theorem weierstrass_approx (a b : ℝ) : Dense (polyFuncs a b) := by
  rw [polyFuncs_eq_coe, dense_iff_closure_eq]
  have h : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
    polynomialFunctions_closure_eq_top a b
  have := congrArg (fun S : Subalgebra ℝ C(Set.Icc a b, ℝ) => (S : Set C(Set.Icc a b, ℝ))) h
  simpa [Subalgebra.topologicalClosure] using this

/-- Epsilon form of the Weierstrass approximation theorem: every continuous function on `[a, b]`
is uniformly approximated to within any `ε > 0` by a polynomial. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  refine ⟨p, fun x => ?_⟩
  have := (ContinuousMap.norm_lt_iff _ hε).1 hp x
  simpa [Real.norm_eq_abs] using this

/-- Weierstrass approximation for unbundled functions: a function `ℝ → ℝ` continuous on `[a, b]`
is uniformly approximated on `[a, b]` to within any `ε > 0` by a polynomial. -/
theorem weierstrass_approx_continuousOn (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
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

