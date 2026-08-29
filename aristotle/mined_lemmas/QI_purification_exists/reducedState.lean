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

noncomputable def reducedState (ψ : H × K → ℂ) : Matrix H H ℂ :=
  Matrix.of fun i j => ∑ k, ψ (i, k) * conj (ψ (j, k))

/-- `ψ`, a vector of the composite system `H ⊗ K`, is a purification of the state `ρ` on `H`
if tracing out the ancilla `K` returns `ρ`. -/
