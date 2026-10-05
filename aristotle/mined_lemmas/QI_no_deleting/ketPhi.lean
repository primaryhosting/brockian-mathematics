import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization notes.

We model a single qubit as `EuclideanSpace ℂ (Fin 2)` and a pair of qubits as
`EuclideanSpace ℂ (Fin 2 × Fin 2)`, with `QI.tens a b` the product (tensor) state
`(i, j) ↦ a i * b j`.

The no-deleting theorem states that there is no unitary `U` on the two-qubit system
which maps `ψ ⊗ ψ` to `ψ ⊗ |0⟩` for every (unknown) unit vector `ψ`; i.e. no unitary
can delete one of two identical copies of an arbitrary state.

The proof: a unitary preserves inner products, and `⟪ψ ⊗ ψ, φ ⊗ φ⟫ = ⟪ψ, φ⟫ ^ 2`
while `⟪ψ ⊗ |0⟩, φ ⊗ |0⟩⟫ = ⟪ψ, φ⟫`, so we would need `c ^ 2 = c` for the overlap `c`
of any two unit vectors. Taking `ψ = |0⟩` and `φ = (3/5) |0⟩ + (4/5) |1⟩` gives
`c = 3/5`, and `9/25 ≠ 3/5`.
-/

open scoped InnerProductSpace

namespace QI

/-- The product (tensor) state of two qubits, `(i, j) ↦ a i * b j`. -/

noncomputable def ketPhi : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![3 / 5, 4 / 5]

