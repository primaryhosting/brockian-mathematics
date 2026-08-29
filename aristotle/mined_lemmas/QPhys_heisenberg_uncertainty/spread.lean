/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module doc-comment `/-! ... -/`, so the
-- header above is written as a plain block comment and repeated as a docstring below.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ` of an operator `A` in the state `ψ`.
For a symmetric (observable) operator and a normalized state this is the physical
expectation value; we take the real part so that it is a real number by construction. -/

noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (expect A ψ : ℂ) • ψ‖

/-- Expansion of the inner product of two centred vectors. -/
