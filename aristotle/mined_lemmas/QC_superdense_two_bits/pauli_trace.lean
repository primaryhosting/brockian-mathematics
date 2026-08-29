/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module doc-comment `/-! ... -/`, so the
-- header above is written as a plain block comment with identical text.)

import Mathlib

/-!
## Superdense coding

Alice and Bob share the Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` in `ℂ² ⊗ ℂ²`.  We represent a
two-qubit state as a `2 × 2` complex matrix `M`, where `M i j` is the amplitude of `|i j⟩`;
in this picture `|Φ⁺⟩` is `(√2)⁻¹ • 1` and acting by a unitary `U` on Alice's (first) qubit is
left multiplication `U * M`.

To send the two classical bits `(b₁, b₂)` Alice applies the Pauli operator `Z^b₁ X^b₂` to her
single qubit and sends it to Bob.  The resulting four states are the four Bell states; we show
they are orthonormal (`QC.encode_orthonormal`) and hence that the encoding is injective on the
four messages (`QC.superdense_two_bits`): two classical bits have been transmitted through one
qubit plus prior entanglement.  A decoder therefore exists (`QC.exists_decoder`).
-/

namespace QC

open Matrix

/-- The Pauli `X` gate. -/

theorem pauli_trace (a b c d : Bool) :
    Matrix.trace ((pauli a b)ᴴ * pauli c d) = if (a = c ∧ b = d) then 2 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [pauli, pauliX, pauliZ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_fin_two]

/-- The four encoded states are orthonormal. -/
