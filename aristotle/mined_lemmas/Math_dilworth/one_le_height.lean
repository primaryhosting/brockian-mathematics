/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/

lemma one_le_height (x : α) : 1 ≤ height x := by
  classical
  have hsub : ({x} : Finset α) ⊆ Finset.univ.filter (fun y => y ≤ x) := by
    intro y hy
    simp only [Finset.mem_singleton] at hy
    subst hy
    simp
  have := card_le_maxChainCardIn hsub (by simp [Set.Subsingleton.isChain])
  simpa [height] using this

/-- The height is bounded by the length of a longest chain. -/
