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

namespace Math

open Polynomial

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in the space
`C([a,b], ℝ)` of real-valued continuous functions on a compact interval, equipped with the
sup-norm topology. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense {g : C(Set.Icc a b, ℝ) | ∃ p : ℝ[X], ∀ x : Set.Icc a b, g x = p.eval (x : ℝ)} := by
  have hset : {g : C(Set.Icc a b, ℝ) | ∃ p : ℝ[X], ∀ x : Set.Icc a b, g x = p.eval (x : ℝ)}
      = (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
    rw [polynomialFunctions_coe]
    ext g
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, by ext x; simpa using (hp x).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, by intro x; simp⟩
  rw [hset, dense_iff_closure_eq]
  have h1 := polynomialFunctions_closure_eq_top a b
  have h2 : ((polynomialFunctions (Set.Icc a b)).topologicalClosure : Set C(Set.Icc a b, ℝ))
      = (⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) := by rw [h1]
  simpa using h2

/-- Epsilon form of the Weierstrass approximation theorem: every continuous function on `[a,b]`
is uniformly approximated to within any `ε > 0` by a polynomial. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  rw [ContinuousMap.norm_lt_iff _ hε] at hp
  exact ⟨p, fun x => by simpa using hp x⟩

end Math

