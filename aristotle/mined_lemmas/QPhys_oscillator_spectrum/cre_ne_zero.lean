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

/-!
# The spectrum of the quantum harmonic oscillator, via ladder operators

We formalise the algebraic (ladder-operator) derivation of the spectrum of the quantum
harmonic oscillator.

The data is packaged in `QPhys.Ladder`: a complex inner product space `V` (the space of
"nice" states), an annihilation operator `a`, a creation operator `a†`, mutually adjoint,
satisfying the canonical commutation relation `[a, a†] = 1`, together with a nonzero
vacuum vector annihilated by `a`.

The number operator is `N = a† a` and the Hamiltonian is `H = ℏω (N + 1/2)`.

The main result `QPhys.oscillator_spectrum` says that the eigenvalues of `H` are exactly
the numbers `ℏω (n + 1/2)` for `n : ℕ`.
-/

namespace QPhys

/-- A pair of ladder operators on a complex inner product space, together with a vacuum
vector.  `ann` is the annihilation operator `a`, `cre` is the creation operator `a†`;
they are adjoint to each other and satisfy the canonical commutation relation
`[a, a†] = 1`.  The vector `vac` is a nonzero vacuum state, i.e. `a vac = 0`. -/
structure Ladder (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- the annihilation operator `a` -/
  ann : V →ₗ[ℂ] V
  /-- the creation operator `a†` -/
  cre : V →ₗ[ℂ] V
  /-- `cre` is the adjoint of `ann` -/
  adj : ∀ x y : V, inner ℂ (ann x) y = inner ℂ x (cre y)
  /-- the canonical commutation relation `[a, a†] = 1` -/
  comm : ∀ x : V, ann (cre x) - cre (ann x) = x
  /-- the vacuum state -/
  vac : V
  /-- the vacuum state is nonzero -/
  vac_ne_zero : vac ≠ 0
  /-- the vacuum state is annihilated by `a` -/
  ann_vac : ann vac = 0

namespace Ladder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (L : Ladder V)

/-- The number operator `N = a† a`. -/

theorem cre_ne_zero {n : ℕ} {x : V} (hx : x ≠ 0) (h : L.number x = (n : ℂ) • x) :
    L.cre x ≠ 0 := by
  intro hcx
  have h1 := L.inner_cre_cre h
  rw [hcx, inner_zero_left] at h1
  have hxx : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hxx] at h1
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hx' : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    exact_mod_cast hpos.ne'
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, Ne, Nat.cast_eq_zero]
    omega
  rcases mul_eq_zero.1 h1.symm with h' | h'
  · exact hn h'
  · exact hx' h'

/-- Downward induction along the ladder: every eigenvalue of `N` with real part `< n`
is a natural number. -/
