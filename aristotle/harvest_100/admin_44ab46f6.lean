/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- A single-qubit state is a complex amplitude function on the computational basis
`{|0⟩, |1⟩}`, indexed by `Bool` (`false ↦ |0⟩`, `true ↦ |1⟩`). -/
abbrev Qubit := Bool → ℂ

/-- The scalar `1/√2`, as a complex number. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℝ)⁻¹

lemma invSqrt2_mul_invSqrt2 : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

lemma two_mul_invSqrt2_sandwich (x : ℂ) : 2 * (invSqrt2 * (x * invSqrt2)) = x := by
  linear_combination (2 * x) * invSqrt2_mul_invSqrt2

@[simp] lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  rw [invSqrt2, map_inv₀, Complex.conj_ofReal]

/-- The entangled resource pair `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` shared by Alice (qubit 2)
and Bob (qubit 3). -/
noncomputable def bellPair : Bool → Bool → ℂ := fun j k => if j = k then invSqrt2 else 0

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`: qubit 1 is the unknown state to be
teleported, qubits 2 and 3 carry the entangled pair. -/
noncomputable def initialState (psi : Qubit) : Bool → Bool → Bool → ℂ :=
  fun i j k => psi i * bellPair j k

/-- The Bell basis `|B_{m n}⟩` of the two-qubit space, indexed by the two classical
measurement outcome bits `m` (phase bit) and `n` (flip bit):
`|B_{m n}⟩ = (|0, n⟩ + (-1)^m |1, ¬n⟩)/√2`. -/
noncomputable def bellBasis (m n : Bool) : Bool → Bool → ℂ :=
  fun i j => if j = xor i n then (if m && i then -invSqrt2 else invSqrt2) else 0

/-- The four Bell states form an orthonormal basis of the two-qubit space, so
`postMeasurement` below really is the projection onto a genuine measurement outcome. -/
lemma bellBasis_orthonormal (m n m' n' : Bool) :
    ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bellBasis m n i j) * bellBasis m' n' i j =
      if m = m' ∧ n = n' then 1 else 0 := by
  simp only [bellBasis, Fintype.sum_bool]
  cases m <;> cases n <;> cases m' <;> cases n' <;>
    simp [invSqrt2_mul_invSqrt2] <;> norm_num

/-- Alice's Bell-basis measurement on qubits 1 and 2 with outcome `(m, n)`: the
(unnormalized) state left on Bob's qubit 3 is the partial inner product
`(⟨B_{m n}| ⊗ I) |ψ⟩|Φ⁺⟩`. -/
noncomputable def postMeasurement (m n : Bool) (T : Bool → Bool → Bool → ℂ) : Qubit :=
  fun k => ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bellBasis m n i j) * T i j k

/-- Explicit form of Bob's unnormalized conditional state: after the outcome `(m, n)`
Bob holds `(1/2) · (-1)^(m · (k ⊕ n)) · ψ(k ⊕ n)`, i.e. `(1/2) X^n Z^m |ψ⟩`. -/
lemma postMeasurement_initialState (psi : Qubit) (m n k : Bool) :
    postMeasurement m n (initialState psi) k =
      (if m && (xor k n) then -(1 / 2 : ℂ) else (1 / 2 : ℂ)) * psi (xor k n) := by
  simp only [postMeasurement, initialState, bellPair, bellBasis, Fintype.sum_bool]
  cases m <;> cases n <;> cases k <;>
    simp <;>
    first
      | linear_combination psi false * invSqrt2_mul_invSqrt2
      | linear_combination psi true * invSqrt2_mul_invSqrt2

/-- Each of the four Bell outcomes occurs with probability `1/4`, independently of the
input state: this is what the renormalization factor `2` in `teleported` accounts for. -/
lemma postMeasurement_normSq (psi : Qubit) (m n : Bool) :
    ∑ k : Bool, Complex.normSq (postMeasurement m n (initialState psi) k) =
      (1 / 4) * ∑ i : Bool, Complex.normSq (psi i) := by
  simp only [postMeasurement_initialState, Fintype.sum_bool]
  cases m <;> cases n <;>
    simp [Complex.normSq_mul, Complex.normSq_neg] <;> ring

/-- The Pauli `X` (bit-flip) correction, applied when the classical bit `n` is `true`. -/
def pauliX (n : Bool) (phi : Qubit) : Qubit := fun k => phi (xor k n)

/-- The Pauli `Z` (phase-flip) correction, applied when the classical bit `m` is `true`. -/
def pauliZ (m : Bool) (phi : Qubit) : Qubit := fun k => if m && k then -phi k else phi k

/-- Bob's final state after receiving the classical outcome `(m, n)`, applying the
correction `Z^m X^n`, and renormalizing (each outcome occurs with probability `1/4`,
so the amplitudes carry a factor `1/2`). -/
noncomputable def teleported (psi : Qubit) (m n : Bool) : Qubit :=
  fun k => 2 * pauliZ m (pauliX n (postMeasurement m n (initialState psi))) k

/-- **Teleportation identity.** For every input qubit state `|ψ⟩` and every Bell
measurement outcome `(m, n)`, the state of Bob's qubit after the corresponding
Pauli correction `Z^m X^n` (and renormalization) is exactly the input state `|ψ⟩`. -/
theorem teleportation_identity (psi : Qubit) (m n : Bool) :
    teleported psi m n = psi := by
  funext k
  simp only [teleported, pauliZ, pauliX, postMeasurement, initialState, bellPair,
    bellBasis, Fintype.sum_bool]
  cases m <;> cases n <;> cases k <;>
    simp <;> exact two_mul_invSqrt2_sandwich _

end QC

