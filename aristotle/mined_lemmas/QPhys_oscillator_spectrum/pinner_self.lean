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

theorem pinner_self (p : Polynomial ℂ) :
    pinner p p
      = ((∑ n ∈ p.support, (n.factorial : ℝ) * Complex.normSq (p.coeff n) : ℝ) : ℂ) := by
  unfold pinner
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]

