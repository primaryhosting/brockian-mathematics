import Mathlib

/-!
# The no-cloning theorem

We model a single qubit by `Qubit := EuclideanSpace ℂ (Fin 2)` and the two-qubit
space `H ⊗ H` by `TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the tensor
product of vectors given coordinatewise by `Qubit.tens`.

A *unitary* operator on the two-qubit space is a surjective linear isometry, i.e. a
term of type `TwoQubit ≃ₗᵢ[ℂ] TwoQubit`.

The main result `QC.no_cloning` states that for every "blank" vector `blank` and every
unitary `U` there is a state `ψ` (a unit vector) with `U (ψ ⊗ blank) ≠ ψ ⊗ ψ`.
-/

namespace QC

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of two qubit states. -/

lemma norm_e0_add_e1 : ‖e0 + e1‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [e0, e1, Fin.sum_univ_two, EuclideanSpace.single_apply]

/-- The uniform superposition `(|0⟩ + |1⟩)/√2`. -/
