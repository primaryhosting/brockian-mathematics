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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/

theorem harmonic_invariant (c : ℝ) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (x y : ℝ) :
    (f' x) ^ 2 + c * (f x) ^ 2 = (f' y) ^ 2 + c * (f y) ^ 2 := by
  set Q : ℝ → ℝ := fun t => (f' t) ^ 2 + c * (f t) ^ 2 with hQ
  have hQd : ∀ t : ℝ, HasDerivAt Q 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (f' t) ^ 2) (2 * f' t * (-c * f t)) t := by
      simpa using ((hf' t).pow 2)
    have h2 : HasDerivAt (fun t : ℝ => c * (f t) ^ 2) (c * (2 * f t * f' t)) t :=
      (((hf t).pow 2).const_mul c).congr_deriv (by ring)
    have h3 := h1.add h2
    convert h3 using 1
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hQd t).differentiableAt)
    (fun t => (hQd t).deriv) x y

/-- Uniqueness: a solution of `f'' = -c f` with `c > 0` vanishing to first order at `0`
is identically zero. -/
