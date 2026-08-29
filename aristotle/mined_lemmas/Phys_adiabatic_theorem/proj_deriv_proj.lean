/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped InnerProductSpace

namespace Phys

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Setup

Throughout, `H s` is a time–dependent (self-adjoint) Hamiltonian, `Ev s` a real eigenvalue,
and `P s` the orthogonal projection onto the corresponding eigenspace.  `P₁`, `P₂` are the
first and second derivatives of `P`, `H'` the derivative of `H` and `Ev'` the derivative of `Ev`.
-/

section Defs

variable (H H' P P₁ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)

/-- The shifted Hamiltonian `H s - Ev s` with the eigenprojection added, so that it becomes
invertible exactly when `Ev s` is an isolated (gapped) eigenvalue. -/

lemma proj_deriv_proj (hPidem : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (s : ℝ) :
    P s * P₁ s * P s = 0 := by
  have h := proj_deriv_decomp hPidem hP s
  have h2 : P s * (P s * P₁ s + P₁ s * P s) = P s * P₁ s := by rw [h]
  rw [mul_add, ← mul_assoc, hPidem s, ← mul_assoc] at h2
  exact add_left_cancel (h2.trans (add_zero (P s * P₁ s)).symm)

/-- Pure ring-theoretic form of the commutator identity. -/
