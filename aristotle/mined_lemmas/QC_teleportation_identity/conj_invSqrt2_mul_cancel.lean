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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- A one-qubit state: a vector of amplitudes indexed by the computational basis
`{|0⟩, |1⟩}`. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- `1/√2`, the normalisation constant of the Bell states. -/

lemma conj_invSqrt2_mul_cancel (z : ℂ) :
    (starRingEnd ℂ) invSqrt2 * z * invSqrt2 * 2 = z := by
  rw [conj_invSqrt2]
  linear_combination (2 * z) * invSqrt2_mul_self

/-- The Pauli `X` (bit flip) gate acting on a qubit state. -/
