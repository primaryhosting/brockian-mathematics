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

noncomputable def expect (v : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, ∑ j, conj (v i) * (M i j * v j)

/-- The commutator `[H, A] = H A - A H` of two matrices. -/
