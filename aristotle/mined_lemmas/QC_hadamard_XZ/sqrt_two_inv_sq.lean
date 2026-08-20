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

lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ)) * ((Real.sqrt 2 : ℝ)) = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hne : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro hz
    rw [hz] at h2
    norm_num at h2
  field_simp
  linear_combination -h2

/-- `H = (X + Z)/√2`, and `H X H = Z`. -/
