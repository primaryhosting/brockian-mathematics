/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The Pauli `X` matrix. -/

theorem H_eq_add_div : H = (sqrt2)⁻¹ • (X + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, X, Z, Matrix.smul_apply, one_div]

/-- `H * X * H = Z`. -/
