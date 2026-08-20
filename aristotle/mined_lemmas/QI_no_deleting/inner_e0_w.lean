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

lemma inner_e0_w : inner ℂ e0 w = (3 / 5 : ℂ) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, e0, w, Fin.sum_univ_two]

/-!
## The key intermediate lemma

Any map preserving inner products which deletes would force `⟪ψ, φ⟫ ^ 2 = ⟪ψ, φ⟫`
for all unit vectors `ψ, φ`, since
`⟪ψ ⊗ ψ, φ ⊗ φ⟫ = ⟪ψ, φ⟫ ^ 2` while `⟪ψ ⊗ |0⟩, φ ⊗ |0⟩⟫ = ⟪ψ, φ⟫`.
This is impossible: the overlap of two unit vectors can be `3/5`, and `(3/5)^2 ≠ 3/5`.
-/

/-- Key lemma: there is no inner-product preserving map that deletes an unknown qubit. -/
