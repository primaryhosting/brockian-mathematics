import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/

theorem det_eq_mertens_4 : R4.det = -1 := by
  simp [R4, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The Mertens function value `M 4 = μ 1 + μ 2 + μ 3 + μ 4 = -1` equals `det R4`. -/
