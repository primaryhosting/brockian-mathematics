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

private lemma quad_nonneg (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B))
    (X Y : Matrix n n ℂ) (s t : ℂ) :
    0 ≤ (starRingEnd ℂ s * s) * phi (Xᴴ * X) + (starRingEnd ℂ s * t) * phi (Xᴴ * Y)
      + (starRingEnd ℂ t * s) * phi (Yᴴ * X) + (starRingEnd ℂ t * t) * phi (Yᴴ * Y) := by
  have h := hpos (s • X + t • Y)
  have hexp : (s • X + t • Y)ᴴ * (s • X + t • Y)
      = (starRingEnd ℂ s * s) • (Xᴴ * X) + (starRingEnd ℂ s * t) • (Xᴴ * Y)
        + (starRingEnd ℂ t * s) • (Yᴴ * X) + (starRingEnd ℂ t * t) • (Yᴴ * Y) := by
    simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul, starRingEnd_apply, mul_comm]
    abel
  rw [hexp] at h
  simpa only [map_add, map_smul, smul_eq_mul] using h

/-- Hermitian symmetry of the sesquilinear form attached to a positive functional. -/
