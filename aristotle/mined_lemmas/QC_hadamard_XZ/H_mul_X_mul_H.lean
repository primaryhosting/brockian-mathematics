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

theorem H_mul_X_mul_H : H * X * H = Z := by
  have hs := sqrt2_sq
  have hne := sqrt2_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, X, Z, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;>
    first
      | linear_combination hs
      | linear_combination -hs

/-- **Hadamard XZ**: `H = (X + Z)/√2` and `H X H = Z`. -/
