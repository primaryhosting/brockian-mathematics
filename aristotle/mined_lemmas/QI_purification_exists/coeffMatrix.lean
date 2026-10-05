import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

def coeffMatrix (ψ : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i j => ψ (i, j)

/-- `ψ`, a state vector of the composite system `H_A ⊗ H_B`, is a *purification* of the
state `ρ` on `H_A` when tracing out the ancilla `H_B` from `|ψ⟩⟨ψ|` returns `ρ`. -/
