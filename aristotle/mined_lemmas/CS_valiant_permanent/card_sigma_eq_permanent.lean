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

lemma card_sigma_eq_permanent :
    Fintype.card ((π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i)))) = A.permanent := by
  rw [Fintype.card_sigma, ← Matrix.permanent_transpose]
  unfold Matrix.permanent
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => Fintype.card_fin _

/-- The permanent of the 0/1 gadget matrix equals the weighted permanent of `A`. -/
