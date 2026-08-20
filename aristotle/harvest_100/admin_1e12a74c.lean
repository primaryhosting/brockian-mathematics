import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

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

/--
**Carbon skeleton of an acyclic alkane.**

Model: the `n` carbon atoms of a saturated acyclic hydrocarbon are the vertices of a
simple graph `G` whose edges are the C–C bonds. Saturation and connectivity of the
molecule say that `G` is connected, "acyclic alkane" says `G` has no cycles, and
tetravalence of carbon says every carbon carries `H v = 4 - deg(v)` hydrogens
(with `deg v ≤ 4`).

Conclusions:
* the carbon skeleton is a tree;
* it has exactly `n - 1` C–C bonds;
* the molecular formula is `Cₙ H_{2n+2}`.

The bond count is `SimpleGraph.IsTree.card_edgeFinset`; the hydrogen count follows from
the handshake lemma `SimpleGraph.sum_degrees_eq_twice_card_edges`.
-/
theorem alkane_tree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (hn : Fintype.card V = n)
    (hconn : G.Connected) (hacyc : G.IsAcyclic)
    (H : V → ℕ) (hdeg : ∀ v, G.degree v ≤ 4) (hH : ∀ v, H v = 4 - G.degree v) :
    G.IsTree ∧ G.edgeFinset.card = n - 1 ∧ ∑ v, H v = 2 * n + 2 := by
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have hcard : G.edgeFinset.card + 1 = n := by
    rw [← hn]; exact htree.card_edgeFinset
  have hpos : 1 ≤ n := by omega
  refine ⟨htree, by omega, ?_⟩
  -- handshake lemma
  have hsum : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hsplit : (∑ v, H v) + ∑ v, G.degree v = 4 * n := by
    rw [← Finset.sum_add_distrib]
    have : ∀ v ∈ (Finset.univ : Finset V), H v + G.degree v = 4 := by
      intro v _
      have := hdeg v
      rw [hH v]
      omega
    rw [Finset.sum_congr rfl this]
    simp [hn, mul_comm]
  omega

end Chem

