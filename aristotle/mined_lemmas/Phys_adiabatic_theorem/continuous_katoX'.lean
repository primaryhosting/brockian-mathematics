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

lemma continuous_katoX' (hH : ∀ s, HasDerivAt H (H' s) s) (hH' : Continuous H')
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hEv' : Continuous Ev')
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (hP1 : ∀ s, HasDerivAt P₁ (P₂ s) s)
    (hP2 : Continuous P₂)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) :
    Continuous (katoX' H H' P P₁ P₂ Ev Ev') := by
  have hcP : Continuous P :=
    continuous_iff_continuousAt.2 fun s => (hP s).continuousAt
  have hcP1 : Continuous P₁ :=
    continuous_iff_continuousAt.2 fun s => (hP1 s).continuousAt
  have hcinv : Continuous (fun t => Ring.inverse (shiftUnit H P Ev t)) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_ringInverse_comp (M' := shiftUnit' H' P₁ Ev')
        (hasDerivAt_shiftUnit hH hEv hP s) (hgap s)).continuousAt
  have hcS : Continuous (redRes H P Ev) := by
    simpa [redRes] using hcinv.sub hcP
  have hcM' : Continuous (shiftUnit' H' P₁ Ev') := by
    have : Continuous (fun t => ((Ev' t : ℂ)) • (1 : E →L[ℂ] E)) :=
      (Complex.continuous_ofReal.comp hEv').smul continuous_const
    simpa [shiftUnit'] using (hH'.sub this).add hcP1
  have hcS' : Continuous (redRes' H H' P P₁ Ev Ev') := by
    simpa [redRes'] using (((hcinv.mul hcM').mul hcinv).neg).sub hcP1
  simpa [katoX'] using
    ((((hcS'.mul hcP1).mul hcP).add ((hcS.mul hP2).mul hcP)).add ((hcS.mul hcP1).mul hcP1)).sub
      ((((hcP1.mul hcP1).mul hcS).add ((hcP.mul hP2).mul hcS)).add ((hcP.mul hcP1).mul hcS'))

/-! ## The Schrödinger evolution -/

/-- Derivative of `t ↦ ⟪ψ t, A t (ψ t)⟫` along a solution of the Schrödinger equation. -/
