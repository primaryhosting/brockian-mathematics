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

theorem weierstrass_approx_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  rw [ContinuousMap.norm_lt_iff _ hε] at hp
  exact ⟨p, fun x => by simpa using hp x⟩

end Math

