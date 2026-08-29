import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/

def IsDensityMatrix (ρ : Matrix H H ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The reduced density matrix on the system `H` of the pure state `|ψ⟩⟨ψ|` living on
`H ⊗ K`, i.e. the partial trace of `|ψ⟩⟨ψ|` over the ancilla `K`. -/
