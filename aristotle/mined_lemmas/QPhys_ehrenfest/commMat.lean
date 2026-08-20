/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate Finset

variable {n : ℕ}

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an observable `A` (given as a matrix)
in the state `ψ` (a vector of `ℂ^n`). -/

noncomputable def commMat (H A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H * A - A * H

