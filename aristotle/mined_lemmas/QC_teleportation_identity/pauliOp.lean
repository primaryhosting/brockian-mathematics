import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization of the quantum teleportation protocol for a single qubit.

A one-qubit state is a vector `psi : Fin 2 → ℂ`.  The three-qubit input state of the
protocol is `psi ⊗ Φ⁺`, where `Φ⁺` is the Bell state shared by Alice and Bob.
Alice measures her two qubits in the Bell basis `{B₀, B₁, B₂, B₃}`; conditioned on
outcome `k`, Bob's qubit collapses to the (unnormalized) vector `collapsed psi k`,
whose entries are the overlaps `⟨B_k| (psi ⊗ Φ⁺)⟩`.  Bob then applies the Pauli
correction `pauliOp k`.  The theorem `QC.teleportation_identity` states that the
corrected state, after the renormalization by the factor `2` (each outcome occurs
with probability `1/4`, i.e. the collapsed vector has norm `1/2`), is exactly the
input state `psi` — teleportation is exact, for every measurement outcome.

The four correction operators are `I`, `X`, `Z` and `i·Y = !![0,1;-1,0]`, and (a
pleasant coincidence of conventions) the same four matrices, scaled by `1/√2`, are
the amplitude tables of the four Bell states.
-/


set_option maxHeartbeats 1000000

namespace QC

open Matrix Finset

/-- The four one-qubit correction operators used by the teleportation protocol:
`I`, `X`, `Z` and `i·Y`. -/

noncomputable def pauliOp : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![1, 0; 0, -1], !![0, 1; -1, 0]]

/-- The Bell basis of the two-qubit space, given as amplitude tables
`bell k a b = ⟨a b | B_k⟩`:
`B₀ = Φ⁺`, `B₁ = Ψ⁺`, `B₂ = Φ⁻`, `B₃ = Ψ⁻`. -/
