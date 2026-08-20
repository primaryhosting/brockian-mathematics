/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
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

set_option grind.warning false

namespace QC

/-- A one-qubit state is a vector of amplitudes indexed by `Fin 2`. -/
abbrev Qubit := Fin 2 → ℂ

/-- A three-qubit state is an amplitude for each triple of bit values. -/
abbrev Qubit3 := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- `(-1)^(i*k)`, the phase produced by the Pauli-`Z` gate on basis state `k`
raised to the power `i`. -/
noncomputable def zsign (i k : Fin 2) : ℂ := if i = 1 ∧ k = 1 then -1 else 1

/-- The Bell state `(|00⟩ + |11⟩)/√2` of the two qubits shared by Alice and Bob. -/
noncomputable def bell (j k : Fin 2) : ℂ := if j = k then 1 / Real.sqrt 2 else 0

/-- The `2 × 2` Hadamard matrix entries. -/
noncomputable def hadamard (i i' : Fin 2) : ℂ := (1 / Real.sqrt 2) * zsign i i'

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`. -/
noncomputable def initialState (psi : Qubit) : Qubit3 :=
  fun i j k => psi i * bell j k

/-- CNOT with qubit 1 as control and qubit 2 as target. -/
noncomputable def applyCNOT (s : Qubit3) : Qubit3 := fun i j k => s i (j + i) k

/-- Hadamard applied to qubit 1. -/
noncomputable def applyH (s : Qubit3) : Qubit3 :=
  fun i j k => ∑ i' : Fin 2, hadamard i i' * s i' j k

/-- The (unnormalized) state of Bob's qubit after Alice measures qubits 1 and 2
and obtains outcomes `m₁, m₂`. -/
noncomputable def residual (psi : Qubit) (m₁ m₂ : Fin 2) : Qubit :=
  fun k => applyH (applyCNOT (initialState psi)) m₁ m₂ k

/-- Pauli-`X` raised to the power `m` acting on a qubit. -/
noncomputable def applyX (m : Fin 2) (v : Qubit) : Qubit := fun k => v (k + m)

/-- Pauli-`Z` raised to the power `m` acting on a qubit. -/
noncomputable def applyZ (m : Fin 2) (v : Qubit) : Qubit := fun k => zsign m k * v k

/-- Bob's corrected state: apply `X^{m₂}` and then `Z^{m₁}` to the residual state. -/
noncomputable def corrected (psi : Qubit) (m₁ m₂ : Fin 2) : Qubit :=
  applyZ m₁ (applyX m₂ (residual psi m₁ m₂))

/-- **Teleportation identity.**  For every input qubit state `|ψ⟩` and every pair of
classical measurement outcomes `(m₁, m₂)` obtained by Alice, the state of Bob's qubit
after applying the corresponding Pauli correction `Z^{m₁} X^{m₂}` is exactly `|ψ⟩`,
up to the amplitude factor `1/2` (whose squared modulus `1/4` is the probability of
that measurement outcome).  In particular the teleported state, once renormalized,
equals the input state. -/
theorem teleportation_identity (psi : Qubit) (m₁ m₂ : Fin 2) :
    corrected psi m₁ m₂ = (1 / 2 : ℂ) • psi := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have key : ∀ x : ℂ, ((Real.sqrt 2 : ℂ))⁻¹ * (x * ((Real.sqrt 2 : ℂ))⁻¹) = 1 / 2 * x := by
    intro x
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ * (x * ((Real.sqrt 2 : ℂ))⁻¹)
        = x * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ by rw [mul_inv]; ring, hsq]
    ring
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases k <;>
    simp only [corrected, residual, applyZ, applyX, applyH, applyCNOT, initialState,
      hadamard, bell, zsign, Fin.sum_univ_two] <;>
    norm_num <;>
    exact key _

/-- Renormalized form of the teleportation identity: multiplying Bob's corrected
state by the normalization factor `2` returns the input state exactly. -/
theorem teleportation_identity_normalized (psi : Qubit) (m₁ m₂ : Fin 2) :
    (2 : ℂ) • corrected psi m₁ m₂ = psi := by
  rw [teleportation_identity, smul_smul]
  norm_num

end QC

