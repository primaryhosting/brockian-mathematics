/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- A colouring of the poset by `{0, …, n-1}` whose colour classes are antichains. -/

lemma height'_le (x : α) : height' x ≤ longestChain α := by
  refine Finset.sup_le ?_
  intro C hC
  exact card_le_longestChain (mem_chains.mp (Finset.mem_filter.mp hC).1)

