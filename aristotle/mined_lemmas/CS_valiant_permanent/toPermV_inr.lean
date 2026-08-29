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

lemma toPermV_inr (c : Cells A) :
    toPermV A π k (Sum.inr c) =
      if c = cellOf A π k c.1.1 then Sum.inl c.1.2 else Sum.inr c := rfl

/-- Cycle covers of the gadget graph coming from `(π, k)` indeed have all weights `1`. -/
