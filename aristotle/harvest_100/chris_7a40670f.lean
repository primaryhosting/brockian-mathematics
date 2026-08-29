import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A one-qubit state: a vector of amplitudes indexed by the computational basis
`{|0⟩, |1⟩}`. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- `1/√2`, the normalisation constant of the Bell states. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa [invSqrt2] using h

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-- The normalisation bookkeeping of the protocol: the factor `2` restores the
amplitude lost to the two `1/√2` normalisations. -/
lemma conj_invSqrt2_mul_cancel (z : ℂ) :
    (starRingEnd ℂ) invSqrt2 * z * invSqrt2 * 2 = z := by
  rw [conj_invSqrt2]
  linear_combination (2 * z) * invSqrt2_mul_self

/-- The Pauli `X` (bit flip) gate acting on a qubit state. -/
def pauliX (psi : Qubit) : Qubit := fun i => psi (i + 1)

/-- The Pauli `Z` (phase flip) gate acting on a qubit state. -/
def pauliZ (psi : Qubit) : Qubit := fun i => (if i = 0 then 1 else -1) * psi i

/-- `pauliX` raised to the power given by a classical bit `m`. -/
def pauliXPow (m : Fin 2) (psi : Qubit) : Qubit := if m = 0 then psi else pauliX psi

/-- `pauliZ` raised to the power given by a classical bit `m`. -/
def pauliZPow (m : Fin 2) (psi : Qubit) : Qubit := if m = 0 then psi else pauliZ psi

/-- Alice's correction instruction sent to Bob: on measurement outcome `(m₁, m₂)`
Bob applies `X^m₂` and then `Z^m₁`. -/
def correction (m₁ m₂ : Fin 2) (psi : Qubit) : Qubit := pauliZPow m₁ (pauliXPow m₂ psi)

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`, where the unknown qubit `ψ` is the
first tensor factor and `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` is the shared Bell pair
(second factor: Alice, third factor: Bob).  The amplitude of `|i j k⟩` is given. -/
noncomputable def initialState (psi : Qubit) : Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j k => psi i * invSqrt2 * (if j = k then 1 else 0)

/-- The Bell basis on Alice's two qubits:
`|B_{m₁ m₂}⟩ = (|0, m₂⟩ + (-1)^{m₁} |1, m₂ ⊕ 1⟩)/√2`.
For `(m₁,m₂) = (0,0)` this is `|Φ⁺⟩`, and the four vectors form an orthonormal basis. -/
noncomputable def bell (m₁ m₂ : Fin 2) : Fin 2 → Fin 2 → ℂ :=
  fun i j => invSqrt2 * ((if i = 0 ∧ j = m₂ then 1 else 0)
      + (if m₁ = 0 then 1 else -1) * (if i = 1 ∧ j = m₂ + 1 then 1 else 0))

/-- Sanity check: the four vectors `bell m₁ m₂` form an orthonormal basis of the
two-qubit space, so projecting onto them is a legitimate (complete) measurement. -/
lemma bell_orthonormal (m₁ m₂ n₁ n₂ : Fin 2) :
    ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bell m₁ m₂ i j) * bell n₁ n₂ i j
      = if m₁ = n₁ ∧ m₂ = n₂ then 1 else 0 := by
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases n₁ <;> fin_cases n₂ <;>
    simp [bell, Fin.sum_univ_two] <;> ring_nf <;>
    simp [conj_invSqrt2, invSqrt2_mul_self]

/-- Bob's (unnormalised) qubit state after Alice measures her two qubits in the
Bell basis and obtains the outcome `(m₁, m₂)`: the projection of the initial
state onto `|B_{m₁ m₂}⟩` on the first two factors. -/
noncomputable def postMeasurement (psi : Qubit) (m₁ m₂ : Fin 2) : Qubit :=
  fun k => ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bell m₁ m₂ i j) * initialState psi i j k

/--
**Teleportation identity.**  For every input qubit state `ψ` and every Bell-measurement
outcome `(m₁, m₂)`, Bob's post-measurement state (which has norm `1/2` of that of `ψ`,
reflecting the probability `1/4` of the outcome) becomes exactly `ψ` after applying the
correction `Z^{m₁} X^{m₂}`.  Thus the teleportation protocol's post-correction state
equals the input state, for each of the four outcomes.
-/
theorem teleportation_identity (psi : Qubit) (m₁ m₂ : Fin 2) :
    correction m₁ m₂ ((2 : ℂ) • postMeasurement psi m₁ m₂) = psi := by
  funext k
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases k <;>
    simp [correction, pauliZPow, pauliXPow, pauliX, pauliZ, postMeasurement,
      initialState, bell, Fin.sum_univ_two] <;>
    ring_nf <;>
    exact conj_invSqrt2_mul_cancel _

end QC

