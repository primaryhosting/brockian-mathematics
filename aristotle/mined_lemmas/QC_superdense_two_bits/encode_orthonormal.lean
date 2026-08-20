-- (Lean requires `import` to come first in a file; the required header comment follows.)
import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Superdense coding

Alice and Bob share the Bell pair `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.  Alice wants to send two
classical bits `(a, b)` to Bob.  She applies the Pauli operator `Z^b X^a` to *her* qubit
only (one qubit!) and sends it to Bob.  Bob then holds one of the four Bell states
`(Z^b X^a ⊗ I)|Φ⁺⟩`, and these four states are pairwise distinct — indeed pairwise
orthogonal unit vectors — so the two bits are recoverable.

A two-qubit state is modelled as its amplitude array `ψ : Matrix (Fin 2) (Fin 2) ℂ`,
where `ψ i j` is the amplitude of `|i j⟩`.  With this encoding, acting by a one-qubit
operator `U` on the *first* qubit, i.e. `U ⊗ I`, is exactly left multiplication `U * ψ`,
and the Bell state `|Φ⁺⟩` is `(1/√2) • 1`.
-/

namespace QC

open Matrix

/-- Amplitude array of a two-qubit state: `ψ i j` is the amplitude of `|i j⟩`. -/
abbrev TwoQubit := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli `X` (bit flip) gate. -/

theorem encode_orthonormal (m m' : Bool × Bool) :
    inner2 (encode m) (encode m') = if m = m' then 1 else 0 := by
  obtain ⟨a, b⟩ := m
  obtain ⟨a', b'⟩ := m'
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [inner2, encode, pauliOp, bell, PauliX, PauliZ, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, conj_invSqrt2] <;>
    ring_nf <;>
    first
      | rfl
      | linear_combination invSqrt2_sq
      | linear_combination 2 * invSqrt2_sq

#print axioms superdense_two_bits
#print axioms decode_encode
#print axioms encode_orthonormal

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

