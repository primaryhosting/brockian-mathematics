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

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

