/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksCtx_orthogonal (c : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    inner ℝ (ksVec (ksCtx c i)) (ksVec (ksCtx c j)) = (0 : ℝ) := by
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp_all [ksCtx, ksVec, PiLp.inner_apply, Fin.sum_univ_four]

/-- Each context consists of four linearly independent vectors. -/
