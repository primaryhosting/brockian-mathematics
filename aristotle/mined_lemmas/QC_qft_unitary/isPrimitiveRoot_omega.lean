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

set_option grind.warning false

namespace QC

open Complex Finset

/-- The root of unity `exp (2 π i / N)`. -/

lemma isPrimitiveRoot_omega {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (omega N) N := by
  have h := Complex.isPrimitiveRoot_exp N hN
  have : omega N = Complex.exp (2 * Real.pi * Complex.I / N) := rfl
  rw [this]
  convert h using 2

