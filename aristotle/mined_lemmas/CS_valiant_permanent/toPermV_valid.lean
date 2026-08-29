import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma toPermV_valid (v : Vert A) : gadget A v (toPermV A π k v) = 1 := by
  rcases v with i | c
  · rw [toPermV_inl]
    show (if (cellOf A π k i).1.1 = i then 1 else 0) = 1
    rw [show (cellOf A π k i).1.1 = i from rfl, if_pos rfl]
  · rw [toPermV_inr]
    by_cases h : c = cellOf A π k c.1.1
    · rw [if_pos h]
      show (if c.1.2 = c.1.2 then 1 else 0) = 1
      rw [if_pos rfl]
    · rw [if_neg h]
      show (if c = c then 1 else 0) = 1
      rw [if_pos rfl]

