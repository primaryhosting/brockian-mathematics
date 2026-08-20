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

namespace CS

variable {α : Type*}

/-- Merge two lists with respect to a boolean comparison `le`. -/

def msort (le : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      merge le (msort le ((x :: y :: t).take ((t.length + 2) / 2)))
               (msort le ((x :: y :: t).drop ((t.length + 2) / 2)))
termination_by l => l.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- Merging produces a permutation of the concatenation of the two inputs. -/
