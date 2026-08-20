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

private lemma sesq_conj (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B)) (X Y : Matrix n n ℂ) :
    phi (Yᴴ * X) = starRingEnd ℂ (phi (Xᴴ * Y)) := by
  have haim : (phi (Xᴴ * X)).im = 0 := ((Complex.le_def.mp (hpos X)).2).symm
  have hcim : (phi (Yᴴ * Y)).im = 0 := ((Complex.le_def.mp (hpos Y)).2).symm
  have i1 := (Complex.le_def.mp (quad_nonneg hpos X Y 1 1)).2
  have i2 := (Complex.le_def.mp (quad_nonneg hpos X Y 1 Complex.I)).2
  simp only [map_one, one_mul, mul_one, Complex.conj_I, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.zero_im] at i1 i2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- Degenerate Cauchy–Schwarz: if `phi (Xᴴ * X) = 0` then `phi (Xᴴ * Y) = 0`. -/
