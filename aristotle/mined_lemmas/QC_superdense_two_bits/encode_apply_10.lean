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

@[simp] lemma encode_apply_10 (a b : Bool) :
    encode (a, b) 1 0 = if a then (if b then -invSqrt2 else invSqrt2) else 0 := by
  cases a <;> cases b <;>
    simp [encode, pauliOp, bell, PauliX, PauliZ, Matrix.mul_apply, Matrix.one_apply]

