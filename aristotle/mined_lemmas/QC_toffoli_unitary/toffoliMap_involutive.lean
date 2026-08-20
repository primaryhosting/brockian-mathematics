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

open Matrix

/-- The eight classical basis states of a three-qubit register. -/
abbrev Q3 : Type := Fin 2 × Fin 2 × Fin 2

/-- The Toffoli (CCNOT) action on classical basis states: the third (target) bit is
flipped exactly when both control bits are `1`. -/

theorem toffoliMap_involutive : Function.Involutive toffoliMap := by
  intro x; revert x; decide

