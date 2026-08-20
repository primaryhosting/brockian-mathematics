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
