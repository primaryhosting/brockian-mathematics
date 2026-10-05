import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem Tarski_undefinability (code : AForm → Nat) (hcode : Function.Injective code) :
    ¬ ArithDefinableRel (ArithTruth code) := by
  intro hdef
  match hdef with
  | ⟨T, hT⟩ =>
    refine diagonal_truth_not_ArithDefinable code hcode ⟨selfApply T, fun v => ?_⟩
    have h0 : upd v 1 (v 0) 0 = v 0 := by simp [upd]
    have h1 : upd v 1 (v 0) 1 = v 0 := by simp [upd]
    rw [selfApply_sat T v, hT (upd v 1 (v 0)), h0, h1]

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

