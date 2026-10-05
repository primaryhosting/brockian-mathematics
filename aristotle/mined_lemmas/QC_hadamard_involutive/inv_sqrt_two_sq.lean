import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
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

open Matrix Complex

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]` as a complex `2 × 2` matrix. -/

lemma inv_sqrt_two_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [← Real.sqrt_inv, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
  norm_num

/-- The Hadamard gate is self-adjoint (Hermitian): `Hᴴ = H`. -/
