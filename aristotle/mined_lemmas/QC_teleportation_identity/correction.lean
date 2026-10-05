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

noncomputable def correction (m n : Fin 2) (chi : Fin 2 → ℂ) (k : Fin 2) : ℂ :=
  (-1 : ℂ) ^ ((m : ℕ) * (k : ℕ)) * chi (k + n)

/-- Sanity check on the definitions: the four Bell states really do form an
orthonormal basis of the two–qubit space, so the Bell measurement above is a
genuine projective measurement. -/
