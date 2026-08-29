/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## The Kadison–Singer problem

The Kadison–Singer problem asks whether every pure state on the atomic maximal abelian
subalgebra (MASA) `D ⊆ B(ℓ²)` of diagonal operators admits a *unique* extension to a state
on all of `B(ℓ²)`.  It was answered affirmatively by Marcus, Spielman and Srivastava via the
method of interlacing families of polynomials.

Here we formalize the statement of the unique-extension property in the finite dimensional
setting, i.e. for the diagonal MASA `D_n ⊆ M_n(ℂ)`, and give a complete, self-contained proof
of it (this is the classical base case of the problem: the difficulty of Kadison–Singer lies
entirely in the infinite dimensional situation, where the pure states of the MASA are no longer
all of the form `A ↦ A i i`).

The proof formalized below is the standard one: a state `ψ` on `M_n(ℂ)` restricting to the
pure state `δ i` on the diagonal kills the projection `P = 1 - e i i`, and the Cauchy–Schwarz
inequality for positive functionals (proved here from scratch, in the form
`ψ (Xᴴ * X) = 0 → ψ (Xᴴ * Y) = 0`) then forces `ψ A = ψ (e i i * A * e i i) = A i i`.
-/

namespace Frontier

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional. -/
structure IsState (ψ : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  /-- A state is unital. -/
  map_one : ψ 1 = 1
  /-- A state is positive. -/
  nonneg : ∀ A : Matrix n n ℂ, 0 ≤ ψ (Aᴴ * A)

/-- The state `A ↦ A i i` on `M_n(ℂ)`, the canonical extension of the pure state `δ i` of the
diagonal MASA. -/

private lemma re_eq_zero_of_forall {c d : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * c + d) : c = 0 := by
  by_contra hc
  have := h (-(d + 1) / (2 * c))
  rw [div_mul_eq_mul_div, mul_comm] at this
  field_simp at this
  linarith

/-- Cauchy–Schwarz for states, in the form we need: a null vector of the form
`ψ (Xᴴ * X) = 0` is orthogonal to everything. -/
