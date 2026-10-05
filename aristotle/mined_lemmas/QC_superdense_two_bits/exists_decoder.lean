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

theorem exists_decoder : ∃ decode : Matrix (Fin 2) (Fin 2) ℂ → Bool × Bool,
    ∀ m, decode (encode m) = m :=
  ⟨Function.invFun encode, fun m => superdense_two_bits (Function.invFun_eq ⟨m, rfl⟩)⟩

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

