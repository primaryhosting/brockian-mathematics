/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Statement: The teleportation protocol's post-correction state equals the input state.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-! ## Quantum teleportation

A single qubit is a vector in `ℂ²`, represented as `Fin 2 → ℂ`.
Multi-qubit states are represented by their coefficient functions on the
computational basis (so a three-qubit state is `Fin 2 → Fin 2 → Fin 2 → ℂ`).
Addition on `Fin 2` is addition mod 2, i.e. the XOR of classical bits.
-/

/-- A one-qubit state vector, given by its coefficients in the basis `|0⟩, |1⟩`. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- The scalar `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

lemma invSqrt2_sq : invSqrt2 ^ 2 = 1 / 2 := by
  rw [sq, invSqrt2_mul_self]

/-- The Pauli `X` (bit flip) gate acting on a qubit. -/
def pauliX (v : Qubit) : Qubit := fun k => v (k + 1)

/-- The Pauli `Z` (phase flip) gate acting on a qubit. -/
def pauliZ (v : Qubit) : Qubit := fun k => (-1 : ℂ) ^ (k : ℕ) * v k

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` shared by Alice and Bob. -/
noncomputable def bellPair : Fin 2 → Fin 2 → ℂ :=
  fun j k => if j = k then invSqrt2 else 0

/-- The Bell basis state `|β_{m₁m₂}⟩ = (|0,m₂⟩ + (-1)^{m₁}|1, 1⊕m₂⟩)/√2`,
in which Alice measures her two qubits. -/
noncomputable def bellBasis (m₁ m₂ : Fin 2) : Fin 2 → Fin 2 → ℂ :=
  fun i j => if j = i + m₂ then invSqrt2 * (-1 : ℂ) ^ ((m₁ : ℕ) * (i : ℕ)) else 0

/-- The four states `|β_{m₁m₂}⟩` form an orthonormal basis of the two-qubit space. -/
lemma bellBasis_orthonormal (m₁ m₂ n₁ n₂ : Fin 2) :
    ∑ i : Fin 2, ∑ j : Fin 2,
        (starRingEnd ℂ) (bellBasis m₁ m₂ i j) * bellBasis n₁ n₂ i j
      = if m₁ = n₁ ∧ m₂ = n₂ then 1 else 0 := by
  have hconj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
    simp [invSqrt2, map_inv₀]
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases n₁ <;> fin_cases n₂ <;>
    simp [bellBasis, Fin.sum_univ_two, hconj] <;>
    ring_nf <;> rw [invSqrt2_sq] <;> ring

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`, with Alice holding qubits 1 and 2
and Bob holding qubit 3. -/
noncomputable def initialState (psi : Qubit) : Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j k => psi i * bellPair j k

/-- Bob's (unnormalized) qubit after Alice's Bell measurement yields the outcome
`(m₁, m₂)`: the projection of the total state onto `|β_{m₁m₂}⟩` on Alice's qubits. -/
noncomputable def bobResidual (psi : Qubit) (m₁ m₂ : Fin 2) : Qubit :=
  fun k => ∑ i : Fin 2, ∑ j : Fin 2,
    (starRingEnd ℂ) (bellBasis m₁ m₂ i j) * initialState psi i j k

/-- Bob's correction operation for the outcome `(m₁, m₂)`: apply `X` if `m₂ = 1`,
then `Z` if `m₁ = 1`. -/
def correction (m₁ m₂ : Fin 2) (v : Qubit) : Qubit :=
  pauliZ^[(m₁ : ℕ)] (pauliX^[(m₂ : ℕ)] v)

/-- Bob's normalized state after correction (the residual has norm `1/2` of `‖ψ‖`). -/
noncomputable def bobFinal (psi : Qubit) (m₁ m₂ : Fin 2) : Qubit :=
  (2 : ℂ) • correction m₁ m₂ (bobResidual psi m₁ m₂)

/-- Explicit formula for Bob's residual state. -/
lemma bobResidual_apply (psi : Qubit) (m₁ m₂ : Fin 2) (k : Fin 2) :
    bobResidual psi m₁ m₂ k = (1 / 2 : ℂ) * (-1 : ℂ) ^ ((m₁ : ℕ) * ((k + m₂ : Fin 2) : ℕ))
      * psi (k + m₂) := by
  have hconj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
    simp [invSqrt2, map_inv₀]
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases k <;>
    simp [bobResidual, bellBasis, initialState, bellPair, Fin.sum_univ_two, hconj] <;>
    ring_nf <;> rw [invSqrt2_sq] <;> ring

/-- **Quantum teleportation**: after Alice's Bell measurement with any outcome
`(m₁, m₂)` and Bob's corresponding Pauli correction, Bob's (renormalized) qubit
is exactly the input state `|ψ⟩`. -/
theorem teleportation_identity (psi : Qubit) (m₁ m₂ : Fin 2) :
    bobFinal psi m₁ m₂ = psi := by
  funext k
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases k <;>
    simp [bobFinal, correction, pauliX, pauliZ, bobResidual_apply]

/-- Each of the four measurement outcomes occurs with probability `1/4`. -/
theorem teleportation_outcome_prob (psi : Qubit) (m₁ m₂ : Fin 2) :
    ∑ k : Fin 2, ‖bobResidual psi m₁ m₂ k‖ ^ 2 = (1 / 4) * ∑ i : Fin 2, ‖psi i‖ ^ 2 := by
  fin_cases m₁ <;> fin_cases m₂ <;>
    simp [Fin.sum_univ_two, bobResidual_apply, mul_pow] <;> ring

end QC

#print axioms QC.teleportation_identity
#print axioms QC.teleportation_outcome_prob

