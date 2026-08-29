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

def atMostOne (m : ℕ) (f : Fin m → Circuit ι) : Circuit ι :=
  bigAnd ((List.finRange m).flatMap fun a => (List.finRange m).map fun b =>
    if a = b then tru else neg (conj (f a) (f b)))

/-- "Exactly one of `f a` holds". -/
