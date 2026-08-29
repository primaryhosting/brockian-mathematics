import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
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

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

theorem A6_mul_P6 : A6 * P6 = P6 * diagonal eig6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, P6, eig6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal] <;> norm_num

/-- `P6`, as a unit of the matrix ring. -/
