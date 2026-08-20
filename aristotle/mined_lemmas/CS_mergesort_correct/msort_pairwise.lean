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

theorem msort_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (l : List α) :
    (msort le l).Pairwise (fun a b => le a b = true) := by
  induction l using CS.msort.induct with
  | case1 => simp [msort]
  | case2 x => simp [msort]
  | case3 x y t ih1 ih2 =>
      rw [msort]
      exact merge_pairwise le trans total _ _ ih1 ih2

/-- **Correctness of merge sort**: for a transitive and total boolean comparison `le`,
`msort le l` is sorted with respect to `le` and is a permutation of `l`. -/
