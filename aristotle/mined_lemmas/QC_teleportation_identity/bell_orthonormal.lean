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

theorem bell_orthonormal (k l : Fin 4) :
    ∑ a : Fin 2, ∑ b : Fin 2, (starRingEnd ℂ) (bell k a b) * bell l a b
      = if k = l then 1 else 0 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hinv : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, h]
    norm_num
  fin_cases k <;> fin_cases l <;>
    simp [bell, pauliOp, Fin.sum_univ_succ, Complex.conj_ofReal] <;>
    linear_combination 2 * hinv

/-- The Bell-basis decomposition underlying the protocol:
`psi ⊗ Φ⁺ = (1/2) • ∑ k, B_k ⊗ (pauliOp k)ᵀ psi`. -/
