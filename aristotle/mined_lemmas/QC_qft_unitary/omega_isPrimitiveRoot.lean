import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma omega_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (omega N) N :=
  Complex.isPrimitiveRoot_exp N hN

