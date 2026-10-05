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

lemma redRes_mul_sub (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    redRes H P Ev s * (H s - ((Ev s : ℂ)) • 1) = 1 - P s := by
  rw [redRes, sub_mul, proj_mul_sub hHsa hPsa heig s, sub_zero,
    sub_eq_shiftUnit_sub_proj (H := H) (P := P) (Ev := Ev) s, mul_sub,
    Ring.inverse_mul_cancel _ (hgap s), inv_mul_proj hPidem heig hgap s]

/-- `(H - Ev) S = 1 - P`. -/
