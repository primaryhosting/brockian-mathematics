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

theorem teleportation_decomposition (psi : Fin 2 → ℂ) (a b c : Fin 2) :
    inputState psi a b c
      = (1 / 2 : ℂ) * ∑ k : Fin 4, bell k a b * ((pauliOp k)ᵀ.mulVec psi) c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [inputState, bell, pauliOp, Fin.sum_univ_succ, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply] <;>
    ring

end QC


import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

