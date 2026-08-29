import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
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

open Matrix SimpleGraph

/-- A primitive 19-th root of unity. -/

theorem isUnit_dft19 : IsUnit dft19 := by
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  have hdet : dft19.det * dft19inv.det = 1 := by
    rw [← Matrix.det_mul, dft19_mul_inv, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

