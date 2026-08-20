import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setup

We work with a single qubit `Qubit = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`Qubit2 = EuclideanSpace ℂ (Fin 2 × Fin 2)`, which is the tensor square of `Qubit`
(with the product basis indexed by `Fin 2 × Fin 2`).

A *deleting machine* would be a unitary `U` on the two-qubit space with
`U (ψ ⊗ ψ) = ψ ⊗ |0⟩` for every unit vector `ψ`, i.e. it erases the second copy of an
unknown state.  The no-deleting theorem says no such unitary exists.
-/

namespace QI

noncomputable section

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. the tensor square of `Qubit`. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product (tensor) state `x ⊗ y`. -/

lemma norm_w : ‖w‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [w, Fin.sum_univ_two]

