/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a file, so the header above is a
-- plain block comment; the identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

/-! ## Basic notions

A qubit state is an amplitude vector indexed by `Fin 2`; a three-qubit register state is
an amplitude array indexed by `Fin 2 × Fin 2 × Fin 2` (written in curried form).
Addition on `Fin 2` is exactly the XOR of classical bits.

Mathlib has no development of the quantum teleportation protocol (there is no lemma that
`exact?`/`rw?` can apply here), so the protocol is set up from scratch below; the proof
itself only uses `Real.mul_self_sqrt` from Mathlib together with ring normalisation. -/

/-- Amplitude vector of a single qubit. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- Amplitude array of a three-qubit register. -/
abbrev State3 : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The normalisation constant `1/√2`. -/

@[simp] lemma sign_zero : sign 0 = 1 := rfl
