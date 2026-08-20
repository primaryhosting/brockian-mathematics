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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The Pauli `X` matrix. -/

lemma H_eq : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, X, Z]

/-- `H X H = Z`. -/
