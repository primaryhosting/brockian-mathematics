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

/-
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem ofPred_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) : (ofPred f).Ok Q (s + 1) :=
  ⟨HasFml.mono h (by omega), HasFml.mono (HasFml.const (Q := Q) false) (by omega),
    by intro a _ hb; simp [ofPred] at hb⟩

/-! #### The constant one, with a prescribed witness length -/

/-- The gap function with constant value `1`, using witnesses of length `k` (only the
all-zero witness counts). -/
