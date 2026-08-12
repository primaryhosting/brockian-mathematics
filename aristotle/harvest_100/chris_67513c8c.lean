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
noncomputable def PauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` (phase flip) gate. -/
noncomputable def PauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The normalisation constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bell : TwoQubit := invSqrt2 • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Alice's one-qubit encoding operator for the message `(a, b)`: `Z^b X^a`. -/
noncomputable def pauliOp (a b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if b then PauliZ else 1) * (if a then PauliX else 1)

/-- Superdense coding: Alice encodes the two classical bits `m = (a, b)` by applying
`Z^b X^a` to her half of the shared Bell pair (a single qubit). -/
noncomputable def encode (m : Bool × Bool) : TwoQubit := pauliOp m.1 m.2 * bell

/-- The Hermitian inner product on two-qubit amplitude arrays. -/
noncomputable def inner2 (φ ψ : TwoQubit) : ℂ := ∑ i, ∑ j, (starRingEnd ℂ) (φ i j) * ψ i j

lemma invSqrt2_ne_zero : invSqrt2 ≠ 0 := by simp [invSqrt2]

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [invSqrt2, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = ((Real.sqrt 2) * (Real.sqrt 2))⁻¹ by ring,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

@[simp] lemma encode_apply_00 (a b : Bool) : encode (a, b) 0 0 = if a then 0 else invSqrt2 := by
  cases a <;> cases b <;>
    simp [encode, pauliOp, bell, PauliX, PauliZ, Matrix.mul_apply, Matrix.one_apply]

@[simp] lemma encode_apply_11 (a b : Bool) :
    encode (a, b) 1 1 = if a then 0 else (if b then -invSqrt2 else invSqrt2) := by
  cases a <;> cases b <;>
    simp [encode, pauliOp, bell, PauliX, PauliZ, Matrix.mul_apply, Matrix.one_apply]

@[simp] lemma encode_apply_10 (a b : Bool) :
    encode (a, b) 1 0 = if a then (if b then -invSqrt2 else invSqrt2) else 0 := by
  cases a <;> cases b <;>
    simp [encode, pauliOp, bell, PauliX, PauliZ, Matrix.mul_apply, Matrix.one_apply]

lemma neg_invSqrt2_ne : -invSqrt2 ≠ invSqrt2 := by
  intro hc
  exact invSqrt2_ne_zero (by linear_combination -hc / 2)

open Classical in
/-- Bob's decoder: from the received two-qubit state he reads off both classical bits.
(This is exactly the Bell-basis measurement, written on amplitudes: the `(0,0)` amplitude
vanishes iff the first bit is `1`, and the sign of the surviving amplitude gives the
second bit.) -/
noncomputable def decode (ψ : TwoQubit) : Bool × Bool :=
  let a : Bool := decide (ψ 0 0 = 0)
  let b : Bool := if a then decide (ψ 1 0 ≠ invSqrt2) else decide (ψ 1 1 ≠ invSqrt2)
  (a, b)

/-- Bob recovers **both** classical bits from the single qubit Alice sent. -/
theorem decode_encode (m : Bool × Bool) : decode (encode m) = m := by
  obtain ⟨a, b⟩ := m
  cases a <;> cases b <;> simp [decode, invSqrt2_ne_zero, neg_invSqrt2_ne]

/-- **Superdense coding transmits two classical bits.**  The encoding of the four
two-bit messages by a single-qubit Pauli operation on half of a shared Bell pair is
injective, so Bob can recover both bits. -/
theorem superdense_two_bits : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-- The four encoded states form an **orthonormal** family: Bob's four possible states are
pairwise orthogonal unit vectors, hence perfectly distinguishable by a measurement in the
Bell basis. -/
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

