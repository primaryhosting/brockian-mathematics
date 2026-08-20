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

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma rk_le_longestChain (x : α) : rk x ≤ longestChain α := by
  refine Finset.sup_le ?_
  intro C hC
  rw [mem_chainsBelow] at hC
  exact Finset.le_sup (f := Finset.card) (mem_allChains.2 hC.1)

/-- Level sets of the rank function are antichains. -/
