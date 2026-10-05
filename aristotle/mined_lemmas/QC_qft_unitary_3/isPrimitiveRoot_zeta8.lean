import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/

lemma isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8, mul_comm, mul_assoc, mul_left_comm] using this

