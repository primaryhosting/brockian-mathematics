/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-! ## Setup

A two-qubit state is a vector in `ℂ⁴`, with the computational basis ordered as
`|00⟩, |01⟩, |10⟩, |11⟩` (indices `0, 1, 2, 3`).

Alice and Bob share the Bell pair `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, where the first
tensor factor is Alice's qubit and the second is Bob's.  To send two classical
bits `m ∈ {0,1,2,3}`, Alice applies one of the four Pauli operators
`I, X, Z, XZ` **to her single qubit only** (i.e. the operator `P ⊗ I` on the
pair) and sends that one qubit to Bob.  The resulting four states are the four
Bell states; they are orthonormal, hence perfectly distinguishable by Bob, and
in particular the encoding is injective on the four messages.
-/

/-- The normalisation constant `1/√2`, as a complex number. -/
noncomputable def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹

lemma c_ne_zero : c ≠ 0 := by simp [c]

lemma c_conj : (starRingEnd ℂ) c = c := by simp [c, Complex.conj_ofReal]

lemma c_mul_c : c * c = 1 / 2 := by
  have h : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [c, ← mul_inv, ← Complex.ofReal_mul, h]
  norm_num

/-- The shared Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellPhiPlus : Fin 4 → ℂ := ![c, 0, 0, c]

/-- Alice's encoding operators, acting on the two-qubit space: `I ⊗ I`,
`X ⊗ I`, `Z ⊗ I` and `(XZ) ⊗ I`, where the Pauli acts on Alice's qubit. -/
def encodeOp : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![ !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
     !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
     !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
     !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] ]

/-- The superdense-coding encoding: message `m` is encoded as the two-qubit
state obtained by applying the operator `encodeOp m` (a Pauli on Alice's qubit
alone) to the shared Bell pair. -/
noncomputable def encode (m : Fin 4) : Fin 4 → ℂ := (encodeOp m).mulVec bellPhiPlus

/-! ## The four encoded states are the four Bell states -/

lemma encode_zero : encode 0 = ![c, 0, 0, c] := by
  funext i; fin_cases i <;>
    simp [encode, encodeOp, bellPhiPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma encode_one : encode 1 = ![0, c, c, 0] := by
  funext i; fin_cases i <;>
    simp [encode, encodeOp, bellPhiPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma encode_two : encode 2 = ![c, 0, 0, -c] := by
  funext i; fin_cases i <;>
    simp [encode, encodeOp, bellPhiPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma encode_three : encode 3 = ![0, -c, c, 0] := by
  funext i; fin_cases i <;>
    simp [encode, encodeOp, bellPhiPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The four encoded states form an orthonormal family in `ℂ⁴`: Bob can
distinguish them perfectly, recovering both classical bits. -/
theorem encode_orthonormal (i j : Fin 4) :
    ∑ k : Fin 4, (starRingEnd ℂ) (encode i k) * encode j k = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [encode_zero, encode_one, encode_two, encode_three, Fin.sum_univ_four, c_conj] <;>
    linear_combination (2 : ℂ) * c_mul_c

/-- **Superdense coding transmits two classical bits.**  Encoding a two-bit
message by acting with a Pauli operator on Alice's single qubit of a shared
Bell pair is injective on the four possible messages, so the two bits are
recoverable from the transmitted qubit together with Bob's half of the pair. -/
theorem superdense_two_bits : Function.Injective encode := by
  intro i j h
  by_contra hij
  have hij' : ∑ k : Fin 4, (starRingEnd ℂ) (encode i k) * encode j k = 0 := by
    rw [encode_orthonormal i j, if_neg hij]
  rw [h] at hij'
  rw [encode_orthonormal j j, if_pos rfl] at hij'
  exact one_ne_zero hij'

end QC

