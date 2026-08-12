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
noncomputable def bell (k : Fin 4) (a b : Fin 2) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * pauliOp k a b

/-- The three-qubit input state of the protocol: the unknown qubit `psi` (register `a`)
tensored with the shared Bell pair `Φ⁺` (registers `b`, `c`). -/
noncomputable def inputState (psi : Fin 2 → ℂ) (a b c : Fin 2) : ℂ :=
  psi a * bell 0 b c

/-- Bob's (unnormalized) qubit after Alice's Bell measurement returns outcome `k`:
the overlap of the input state with the Bell vector `B_k` on registers `a`, `b`. -/
noncomputable def collapsed (psi : Fin 2 → ℂ) (k : Fin 4) (c : Fin 2) : ℂ :=
  ∑ a : Fin 2, ∑ b : Fin 2, (starRingEnd ℂ) (bell k a b) * inputState psi a b c

/-- **Teleportation identity.**  For every Bell-measurement outcome `k`, applying the
corresponding Pauli correction `pauliOp k` to Bob's collapsed qubit and renormalizing
(by the factor `2`) returns exactly the input state `psi`. -/
theorem teleportation_identity (psi : Fin 2 → ℂ) (k : Fin 4) :
    (2 : ℂ) • (pauliOp k).mulVec (collapsed psi k) = psi := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hinv : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, h]
    norm_num
  have key : ∀ z : ℂ,
      2 * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (z * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹)) = z := by
    intro z
    linear_combination (2 * z) * hinv
  funext c
  fin_cases k <;> fin_cases c <;>
    simp [collapsed, inputState, bell, pauliOp, Fin.sum_univ_succ,
      dotProduct, Complex.conj_ofReal] <;>
    exact key _

/-- Sanity check: the four vectors `bell k` form an orthonormal basis of the two-qubit
space. -/
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

