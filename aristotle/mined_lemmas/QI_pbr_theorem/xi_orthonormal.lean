import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

theorem xi_orthonormal (i j : Fin 4) : ip (xi i) (xi j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [xi, tens, ket0, ket1, ketP, ketM, expand] <;> pbr_calc

/-- Completeness of the PBR measurement on the four product preparations: the four
outcome probabilities sum to one. -/
