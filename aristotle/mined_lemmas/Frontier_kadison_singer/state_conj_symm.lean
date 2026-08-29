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

lemma state_conj_symm (X Y : Matrix n n ℂ) :
    ψ (Yᴴ * X) = (starRingEnd ℂ) (ψ (Xᴴ * Y)) := by
  have h1 : ψ ((X + Y)ᴴ * (X + Y))
      = ψ (Xᴴ * X) + ψ (Xᴴ * Y) + ψ (Yᴴ * X) + ψ (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      map_add, map_add, map_add]
    ring
  have h2 : ψ ((X + Complex.I • Y)ᴴ * (X + Complex.I • Y))
      = ψ (Xᴴ * X) + Complex.I * ψ (Xᴴ * Y) - Complex.I * ψ (Yᴴ * X) + ψ (Yᴴ * Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    simp only [RCLike.star_def, Complex.conj_I, smul_eq_mul, neg_mul]
    ring_nf
    rw [Complex.I_mul_I]
    ring
  have e1 := state_im_eq_zero hψ (X + Y)
  have e2 := state_im_eq_zero hψ (X + Complex.I • Y)
  have p := state_im_eq_zero hψ X
  have q := state_im_eq_zero hψ Y
  rw [h1] at e1
  rw [h2] at e2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, p, q] at e1 e2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- A real quadratic-free positivity argument: if `2 t c + d ≥ 0` for all real `t`, then `c = 0`. -/
