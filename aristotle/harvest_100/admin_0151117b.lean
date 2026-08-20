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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-! ## Setup

A two–qubit state is a function `Fin 2 → Fin 2 → ℂ`, where the first index is
Alice's qubit and the second index is Bob's qubit.

The protocol: Alice and Bob share the Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.  To send the two classical bits `(a, b)`, Alice
applies the Pauli operator `X^a Z^b` **to her qubit only** and sends that single
qubit to Bob.  The four resulting global states are the four Bell states; they
are orthonormal, hence perfectly distinguishable by Bob, so two classical bits
have been transmitted using one qubit plus prior entanglement.
-/

/-- The normalisation constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_conj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2]

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

lemma invSqrt2_sq : invSqrt2 ^ 2 = 1 / 2 := by
  rw [sq, invSqrt2_mul_self]

/-- The Pauli operator `X^a Z^b` applied by Alice for the message `(a, b)`. -/
noncomputable def pauli : Bool → Bool → Matrix (Fin 2) (Fin 2) ℂ
  | false, false => !![1, 0; 0, 1]
  | true,  false => !![0, 1; 1, 0]
  | false, true  => !![1, 0; 0, -1]
  | true,  true  => !![0, -1; 1, 0]

/-- The shared Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bell : Fin 2 → Fin 2 → ℂ :=
  fun i j => if i = j then invSqrt2 else 0

/-- Alice's encoding of the two classical bits `m = (a, b)`: she applies
`X^a Z^b` to her own qubit (the first tensor factor) of the shared Bell pair. -/
noncomputable def encode (m : Bool × Bool) : Fin 2 → Fin 2 → ℂ :=
  fun i j => ∑ k, pauli m.1 m.2 i k * bell k j

/-- The Hermitian inner product on two–qubit states. -/
noncomputable def ip (u v : Fin 2 → Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (u i j) * v i j

lemma encode_apply (m : Bool × Bool) (i j : Fin 2) :
    encode m i j = pauli m.1 m.2 i j * invSqrt2 := by
  simp [encode, bell, Finset.sum_ite_eq' Finset.univ j]

/-- The four encoded states are orthonormal, hence perfectly distinguishable. -/
theorem ip_encode (m m' : Bool × Bool) :
    ip (encode m) (encode m') = if m = m' then 1 else 0 := by
  obtain ⟨a, b⟩ := m
  obtain ⟨a', b'⟩ := m'
  have key : ∀ i j : Fin 2,
      (starRingEnd ℂ) (encode (a, b) i j) * encode (a', b') i j
        = (starRingEnd ℂ) (pauli a b i j) * pauli a' b' i j * (1 / 2) := by
    intro i j
    rw [encode_apply, encode_apply, map_mul, invSqrt2_conj]
    ring_nf
    rw [invSqrt2_sq]
    ring
  simp only [ip, Fin.sum_univ_two, key]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    norm_num [pauli, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Superdense coding transmits two classical bits.**

The encoding `encode : Bool × Bool → (two-qubit states)`, where Alice acts with
a Pauli operator on her single qubit of a shared Bell pair, is injective on the
four messages; indeed the four encoded states are orthonormal, so Bob can
recover both classical bits with certainty by a Bell-basis measurement. -/
theorem superdense_two_bits :
    Function.Injective encode ∧
      (∀ m m' : Bool × Bool, ip (encode m) (encode m') = if m = m' then 1 else 0) := by
  refine ⟨?_, ip_encode⟩
  intro m m' h
  by_contra hne
  have h0 : ip (encode m) (encode m') = 0 := by
    rw [ip_encode, if_neg hne]
  have h1 : ip (encode m) (encode m') = 1 := by
    rw [h, ip_encode, if_pos rfl]
  rw [h0] at h1
  exact zero_ne_one h1

end QC

