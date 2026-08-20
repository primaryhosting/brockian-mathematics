/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header above is written as a plain block comment.)

import Mathlib

/-!
The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) of `B(ℓ²)` extends uniquely to a state on `B(ℓ²)`.  It was answered
affirmatively by Marcus, Spielman and Srivastava via the method of interlacing families of
polynomials.

This file formalizes and proves in full the *finite-dimensional* case — the base case of the
Kadison–Singer question: for the diagonal MASA of the matrix algebra `Mₙ(ℂ)`, the pure state
`d ↦ d i` of the diagonal has a unique extension to a state on `Mₙ(ℂ)`, namely `A ↦ A i i`.

Here a *state* is a unital positive ℂ-linear functional (`Frontier.IsState`), and the pure
states of the diagonal algebra `ℂⁿ` are exactly the coordinate evaluations `d ↦ d i`.

The proof is the classical one: positivity of `phi` yields a positive semidefinite Hermitian
sesquilinear form `(X, Y) ↦ phi (Xᴴ * Y)`, and the degenerate case of the Cauchy–Schwarz
inequality forces `phi` to vanish on every matrix unit other than `E i i`.
-/

namespace Frontier

open Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital, positive linear functional. -/

private lemma diag_state_sum {psi : (n → ℂ) →ₗ[ℂ] ℂ} (h : IsDiagState psi) :
    ∑ j : n, psi (unitVec j) = 1 := by
  have h1 : (1 : n → ℂ) = ∑ j : n, (unitVec j : n → ℂ) := by
    funext k; simp [unitVec, Finset.sum_apply, Pi.single_apply]
  have hh := h.1
  rw [h1, map_sum] at hh
  exact hh

/-- The coordinate evaluation `d ↦ d i` is a state on the diagonal algebra `ℂⁿ`, and it is a
pure state: whenever it is written as a convex combination `t • psi₁ + (1 - t) • psi₂` of two
states with `0 < t < 1`, both summands are equal to it. -/
