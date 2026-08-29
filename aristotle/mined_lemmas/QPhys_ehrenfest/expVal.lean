/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The expectation value `⟨A⟩ (t) = ⟪ψ t, A t (ψ t)⟫` of a (possibly time-dependent)
observable `A` in the state `ψ t`. -/

noncomputable def expVal (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (t : ℝ) : ℂ :=
  inner ℂ (psi t) (A t (psi t))

/-- The commutator `[H, A] = H A - A H` of two operators. -/
