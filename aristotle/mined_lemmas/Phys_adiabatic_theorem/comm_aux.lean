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

lemma comm_aux {R : Type*} [Ring R] (D S Pr Q : R)
    (h1 : S * D = 1 - Pr) (h2 : D * S = 1 - Pr) (h3 : D * Pr = 0) (h4 : Pr * D = 0)
    (h5 : Pr * Q + Q * Pr = Q) (h6 : Pr * Q * Pr = 0) :
    D * (S * Q * Pr - Pr * Q * S) - (S * Q * Pr - Pr * Q * S) * D = Q := by
  have e1 : D * (S * Q * Pr - Pr * Q * S) - (S * Q * Pr - Pr * Q * S) * D
      = (D * S) * Q * Pr - (D * Pr) * Q * S - (S * Q * (Pr * D) - Pr * Q * (S * D)) := by
    noncomm_ring
  rw [e1, h1, h2, h3, h4]
  have e2 : (1 - Pr) * Q * Pr - 0 * Q * S - (S * Q * 0 - Pr * Q * (1 - Pr))
      = (Pr * Q + Q * Pr) - (Pr * Q * Pr) - (Pr * Q * Pr) := by noncomm_ring
  rw [e2, h5, h6, sub_zero, sub_zero]

/-- The commutator equation `[H, X] = P₁`. -/
