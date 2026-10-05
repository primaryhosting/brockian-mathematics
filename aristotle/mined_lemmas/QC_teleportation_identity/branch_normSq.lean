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

lemma branch_normSq (psi : Qubit) (m1 m2 : Fin 2) :
    ∑ c : Fin 2, ‖branch psi m1 m2 c‖ ^ 2 = (1 / 4) * ∑ c : Fin 2, ‖psi c‖ ^ 2 := by
  have hn := norm_invSqrt2_pow_four
  fin_cases m1 <;> fin_cases m2 <;>
    simp [branch, preMeasurement, hadamard1, cnot12, initial, bell, Fin.sum_univ_two,
      mul_comm, mul_pow] <;>
    linear_combination (‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2) * hn

/-- Bob's correction `Z^{m₁} X^{m₂}`, applied to the normalised post-measurement state of
his qubit (the branch rescaled by `2`, cf. `QC.branch_normSq`). -/
