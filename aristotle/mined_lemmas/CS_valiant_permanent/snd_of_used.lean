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

lemma snd_of_used {c : Cells A} (h : c = cellOf A π k c.1.1) : c.1.2 = π c.1.1 :=
  congrArg (fun d : Cells A => d.1.2) h

/-- The cycle cover of the gadget graph determined by a permutation `π` together with a choice
`k` of a cell copy in each row. -/
