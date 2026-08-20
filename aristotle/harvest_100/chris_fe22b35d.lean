/-
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- An (acyclic, saturated) alkane on `n` carbon atoms.

The carbon atoms are indexed by `Fin n`; `skeleton` is the graph of C–C bonds.
An alkane is *acyclic* and *connected* (it is a single molecule), every carbon is
tetravalent, and the valences not used by C–C bonds are saturated with hydrogen:
`degree v + hydrogens v = 4`. -/
structure Alkane (n : ℕ) where
  /-- The carbon skeleton: vertices are carbon atoms, edges are C–C bonds. -/
  skeleton : SimpleGraph (Fin n)
  [decAdj : DecidableRel skeleton.Adj]
  /-- The molecule is a single connected piece. -/
  connected : skeleton.Connected
  /-- The molecule is acyclic. -/
  acyclic : skeleton.IsAcyclic
  /-- The number of hydrogens attached to each carbon. -/
  hydrogens : Fin n → ℕ
  /-- Carbon is tetravalent: C–C bonds plus C–H bonds make four bonds per carbon. -/
  saturated : ∀ v, skeleton.degree v + hydrogens v = 4

attribute [instance] Alkane.decAdj

/-- **Alkane tree theorem.** The carbon skeleton of an acyclic alkane `CₙH₂ₙ₊₂`
is a tree with `n - 1` C–C bonds, and it indeed carries `2n + 2` hydrogens.

The tree part is `SimpleGraph.isTree_iff`, and the bond count is
`SimpleGraph.IsTree.card_edgeFinset` from Mathlib. -/
theorem alkane_tree {n : ℕ} (A : Alkane n) :
    A.skeleton.IsTree ∧
      A.skeleton.edgeFinset.card = n - 1 ∧
      ∑ v, A.hydrogens v = 2 * n + 2 := by
  have htree : A.skeleton.IsTree :=
    (SimpleGraph.isTree_iff _).mpr ⟨A.connected, A.acyclic⟩
  have hcard : A.skeleton.edgeFinset.card + 1 = Fintype.card (Fin n) :=
    htree.card_edgeFinset
  rw [Fintype.card_fin] at hcard
  have hn : 1 ≤ n := by omega
  have hedges : A.skeleton.edgeFinset.card = n - 1 := by omega
  refine ⟨htree, hedges, ?_⟩
  -- Sum the saturation equation over all carbons.
  have hsum : (∑ v, A.skeleton.degree v) + ∑ v, A.hydrogens v = 4 * n := by
    rw [← Finset.sum_add_distrib]
    simp [A.saturated, mul_comm]
  have hdeg : (∑ v, A.skeleton.degree v) = 2 * A.skeleton.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges A.skeleton
  omega

/-- Methane `CH₄`: a single carbon with four hydrogens; a witness that the
hypotheses of `alkane_tree` are satisfiable (the theorem is not vacuous). -/
def methane : Alkane 1 where
  skeleton := ⊥
  connected := by
    constructor
    intro a b
    exact (Subsingleton.elim a b) ▸ SimpleGraph.Reachable.refl a
  acyclic := SimpleGraph.isAcyclic_bot
  hydrogens := fun _ => 4
  saturated := by
    intro v
    have h : (⊥ : SimpleGraph (Fin 1)).degree v = 0 := by
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
    omega

end Chem

