import Mathlib

/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
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

namespace Zeta23Scaffold

/-- The `3 × 3` Hankel moment matrix of the sine kernel (rational entries). -/

lemma sineHankel3_mul_inv : sineHankel3 * sineHankel3Inv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sineHankel3, sineHankel3Inv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

