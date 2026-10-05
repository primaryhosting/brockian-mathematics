/-
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/-- Auxiliary counting step: if every carbon has at most `4` bonds and the total number of
hydrogens `∑ v, (4 - degree v)` equals `2n + 2`, then the number of C–C bonds is `n - 1`. -/

lemma card_edges_of_hydrogen_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (hn : Fintype.card V = n)
    (hval : ∀ v, G.degree v ≤ 4)
    (hH : ∑ v, (4 - G.degree v) = 2 * n + 2) :
    G.edgeFinset.card + 1 = n := by
  have hsum : (∑ v, (4 - G.degree v)) + ∑ v, G.degree v = 4 * n := by
    rw [← Finset.sum_add_distrib]
    have : ∀ v ∈ (Finset.univ : Finset V), (4 - G.degree v) + G.degree v = 4 := fun v _ =>
      Nat.sub_add_cancel (hval v)
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, Finset.card_univ, hn,
      Nat.mul_comm]
  rw [hH, G.sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- **The carbon skeleton of an acyclic alkane is a tree with `n - 1` C–C bonds.**

The carbon skeleton of a molecule is modelled as a simple graph `G` on the set `V` of `n` carbon
atoms, where adjacency means a C–C single bond.  Carbon is tetravalent, so each carbon `v` carries
`4 - G.degree v` hydrogens; the molecular formula `CₙH₂ₙ₊₂` says the total hydrogen count is
`2n + 2`.  Assuming the skeleton is connected (the molecule is a single species), it follows that
`G` is a tree and has exactly `n - 1` C–C bonds.

The key Mathlib ingredients are `SimpleGraph.sum_degrees_eq_twice_card_edges` (handshake lemma)
and `SimpleGraph.isTree_iff_connected_and_card`. -/
