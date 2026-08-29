import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Unconditional base cases -/

/-- A finite group whose order is squarefree is solvable (it is a Z-group). -/

theorem oddOrderSolvable_iff_simpleOddAbelian :
    OddOrderSolvable.{u} ↔ SimpleOddAbelian.{u} := by
  constructor
  · intro h S _ _ hs hodd
    haveI := hs
    exact IsSimpleGroup.comm_iff_isSolvable.mpr (h S hodd)
  · intro h G _ _ hodd
    exact feit_thompson_odd_order h G hodd

end Frontier

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

