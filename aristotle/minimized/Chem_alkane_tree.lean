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

namespace Chem

/-- **The carbon skeleton of an acyclic alkane `CₙH₂ₙ₊₂` is a tree with `n - 1` C–C bonds.**

We model a saturated hydrocarbon as follows.

* `V` is the (finite) set of carbon atoms, `n = #V`;
* `G` is the *carbon skeleton*: `G.Adj u v` means there is a C–C single bond between `u` and `v`
  (a simple graph, so no multiple bonds and no self bonds — the molecule is saturated);
* the molecule is one connected piece: `G.Connected`;
* `hyd v` is the number of hydrogen atoms bonded to the carbon `v`, and each carbon is
  tetravalent: `hyd v + G.degree v = 4`;
* the molecular formula is `CₙH₂ₙ₊₂`: the total number of hydrogens is `2 * n + 2`.

Under these hypotheses the skeleton has exactly `n - 1` C–C bonds and is a tree
(connected and acyclic — in particular the molecule really is *acyclic*, which for alkanes
is a consequence of the formula rather than an extra assumption). -/
theorem alkane_tree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (hconn : G.Connected)
    (hyd : V → ℕ) (hval : ∀ v, hyd v + G.degree v = 4)
    (hH : ∑ v, hyd v = 2 * n + 2) :
    G.edgeFinset.card = n - 1 ∧ G.IsTree := by
  classical
  -- Sum the tetravalence relation over all carbons: `∑ hyd + ∑ degree = 4n`.
  have hsum : (∑ v, hyd v) + ∑ v, G.degree v = 4 * n := by
    rw [← Finset.sum_add_distrib]
    simp [hval, hn, Finset.sum_const, mul_comm]
  -- Handshake lemma: `∑ degree = 2 * #edges`.
  have hdeg : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  rw [hH, hdeg] at hsum
  have hcard : G.edgeFinset.card + 1 = n := by omega
  refine ⟨by omega, ?_⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rwa [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card, hn]

end Chem

