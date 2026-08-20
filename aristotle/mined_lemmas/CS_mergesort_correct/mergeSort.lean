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

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, assumed sorted, into one list. -/

def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
      let l := a :: b :: t
      merge (mergeSort (l.take (l.length / 2))) (mergeSort (l.drop (l.length / 2)))
  termination_by l => l.length
  decreasing_by
  · simp only [List.length_take, List.length_cons]
    omega
  · simp only [List.length_drop, List.length_cons]
    omega

