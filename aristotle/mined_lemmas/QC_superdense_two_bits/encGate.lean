import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- A two-qubit state: `ψ (i, j)` is the amplitude of the basis state `|i⟩ ⊗ |j⟩`.
The first factor is Alice's qubit, the second is Bob's. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Bell state `(|00⟩ + |11⟩)/√2`, shared in advance between Alice and Bob. -/

noncomputable def encGate (a b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if b then pauliZ else 1) * (if a then pauliX else 1)

/-- Superdense coding: Alice encodes the two classical bits `(a, b)` by applying
`encGate a b` to *her own qubit only*; the resulting two-qubit state is one of the
four Bell states. -/
