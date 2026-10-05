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

/-! ## Setup

A qubit state is a vector of amplitudes indexed by `Fin 2`.  Addition on `Fin 2`
is addition modulo `2`, i.e. the classical `xor` used to describe the Pauli `X`
gate and the Bell basis.
-/

/-- The amplitude `1/√2`, as a complex number. -/

noncomputable def postMeasurement (psi : Fin 2 → ℂ) (m n : Fin 2) (k : Fin 2) : ℂ :=
  2 * ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bellBasis m n i j) * inputState psi i j k

/-- Bob's correction operator `Z^m X^n` applied to a one–qubit state. -/
