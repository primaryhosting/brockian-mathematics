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

theorem oscillator_spectrum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (L : Ladder V) {hbar omega : ℝ} (hhbar : 0 < hbar) (homega : 0 < omega) (μ : ℂ) :
    Module.End.HasEigenvalue (L.hamiltonian hbar omega) μ ↔
      ∃ n : ℕ, μ = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) := by
  have hcr : hbar * omega ≠ 0 := by positivity
  have hc : ((hbar * omega : ℝ) : ℂ) ≠ 0 := by
    simpa using hcr
  rw [L.hamiltonian_hasEigenvalue_iff hc μ, L.number_spectrum]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp at hn
    linear_combination hn / 2
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    field_simp
    ring

end QPhys

import RequestProject.Main

set_option maxHeartbeats 1000000

/-!
# A concrete model of the ladder operators: the polynomial Fock space

To show that the hypotheses of `QPhys.oscillator_spectrum` are not vacuous, we exhibit a
concrete system of ladder operators: the space `ℂ[X]` of complex polynomials, equipped
with the inner product

`⟪p, q⟫ = ∑ n, n! * conj (p.coeff n) * q.coeff n`,

with annihilation operator `a = d/dX`, creation operator `a† = (X * ·)` and vacuum the
constant polynomial `1`.  In the (non-normalised) basis `Xⁿ` we have
`a (Xⁿ) = n Xⁿ⁻¹`, `a† (Xⁿ) = Xⁿ⁺¹`, and `⟪Xᵐ, Xⁿ⟫ = n! δₘₙ`.
-/

namespace QPhys.Fock

open Polynomial Finset ComplexConjugate

/-! ### Purely algebraic facts about `d/dX` and `X * ·` -/

/-- The canonical commutation relation `[d/dX, X·] = 1` for polynomials. -/
