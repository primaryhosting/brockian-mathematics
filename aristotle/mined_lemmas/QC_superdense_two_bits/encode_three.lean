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

lemma encode_three : encode 3 = ![0, -c, c, 0] := by
  funext i; fin_cases i <;>
    simp [encode, encodeOp, bellPhiPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The four encoded states form an orthonormal family in `ℂ⁴`: Bob can
distinguish them perfectly, recovering both classical bits. -/
