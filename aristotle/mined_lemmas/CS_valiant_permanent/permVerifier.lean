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

def permVerifier (n : ℕ) : Circuit (Fin (n * n) ⊕ Fin (n * n)) :=
  Circuit.conj
    (Circuit.bigAnd ((List.finRange n).map fun i => Circuit.exactlyOne n (fun j => yvar n i j)))
    (Circuit.conj
      (Circuit.bigAnd ((List.finRange n).map fun j => Circuit.exactlyOne n (fun i => yvar n i j)))
      (Circuit.bigAnd ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
        Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j))))

