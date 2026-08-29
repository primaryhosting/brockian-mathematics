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

lemma card_Vert : Fintype.card (Vert A) = n + ∑ i, ∑ j, A i j := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Fintype.card_fin _

end Gadget

/-- **Weight elimination.** The permanent of an arbitrary matrix of natural-number weights is
the permanent of a 0/1 matrix of size `n + ∑ i j, A i j`.  The 0/1 matrix is built by replacing
the weight `A i j` by `A i j` parallel two-step routes from `i` to `j`, each unused route being
covered by a self-loop; the size is therefore polynomial in `n` and the total weight, i.e.
polynomial in the input size when the weights are written in unary. -/
