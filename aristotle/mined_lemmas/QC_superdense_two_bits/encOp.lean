/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The amplitude `1/√2` of a maximally entangled two-qubit state. -/

noncomputable def encOp (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliX ^ (b : ℕ) * pauliZ ^ (a : ℕ)

/-- The two-qubit state held jointly by Alice and Bob after Alice applies
`X^b Z^a ⊗ I` to `|Φ⁺⟩`; sending her single qubit to Bob conveys the message. -/
