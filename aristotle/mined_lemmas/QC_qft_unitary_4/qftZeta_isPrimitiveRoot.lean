import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

/-- The primitive `16`-th root of unity `exp (2πi/16)` used to build the 4-qubit QFT. -/

lemma qftZeta_isPrimitiveRoot : IsPrimitiveRoot qftZeta 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [qftZeta, mul_comm, mul_assoc, mul_left_comm] using h

