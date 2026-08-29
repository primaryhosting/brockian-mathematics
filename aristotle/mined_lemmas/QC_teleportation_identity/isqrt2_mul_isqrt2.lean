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

@[simp] lemma isqrt2_mul_isqrt2 : isqrt2 * isqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [isqrt2, ← mul_inv, h]
  norm_num

/-- Normalisation bookkeeping: the two factors of `1/√2` cancel the
renormalisation factor `2`. -/
