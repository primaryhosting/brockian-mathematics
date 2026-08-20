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

set_option grind.warning false

namespace Chem

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

lemma cycAdj_apply (j m : ZMod 18) :
    cycAdj j m = if (m = j - 1 ∨ m = j + 1) then 1 else 0 := by
  rw [cycAdj, SimpleGraph.adjMatrix_apply]
  simp only [cyc_adj_iff]

