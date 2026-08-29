/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A single-qubit state is a complex amplitude function on the computational basis
`{|0⟩, |1⟩}`, indexed by `Bool` (`false ↦ |0⟩`, `true ↦ |1⟩`). -/
abbrev Qubit := Bool → ℂ

/-- The scalar `1/√2`, as a complex number. -/

lemma two_mul_invSqrt2_sandwich (x : ℂ) : 2 * (invSqrt2 * (x * invSqrt2)) = x := by
  linear_combination (2 * x) * invSqrt2_mul_invSqrt2

