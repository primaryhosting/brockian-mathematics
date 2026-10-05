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

theorem qft_conjTranspose_mul_self (n : ℕ) : Matrix.conjTranspose (qft n) * qft n = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (qft_unitary n)

/-- Unitarity of the QFT, spelled out: `F * Fᴴ = 1`. -/
