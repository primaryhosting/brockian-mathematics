/- (header comment; Lean requires `import` to be the first command, so the header
   below is a plain block comment rather than a module docstring)
/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QPhys

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation value of a (symmetric) operator `A` in the state `psi`. -/

noncomputable def expect (A : H →ₗ[ℂ] H) (psi : H) : ℝ := (inner ℂ psi (A psi)).re

/-- The spread (standard deviation) of `A` in the state `psi`:
`Δ A = ‖(A - ⟨A⟩) psi‖`. -/

noncomputable def spread (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - ((expect A psi : ℝ) : ℂ) • psi‖

/-- For a symmetric operator, the expectation value is the full inner product (it is real). -/
