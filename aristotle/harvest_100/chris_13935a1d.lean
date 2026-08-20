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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The number of hydrogen atoms attached to a carbon skeleton `G`: every carbon is
tetravalent, so a carbon `v` carries `4 - deg(v)` hydrogens. -/
noncomputable def hydrogenCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  ∑ v, (4 - G.degree v)

/-- Counting hydrogens: `H = 4n - 2·(number of C–C bonds)`. -/
lemma hydrogenCount_add_twice_bonds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 4) :
    hydrogenCount G + 2 * G.edgeFinset.card = 4 * n := by
  have hsum : (∑ v, (4 - G.degree v)) + ∑ v, G.degree v = ∑ _v : Fin n, 4 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Nat.sub_add_cancel (hdeg v)
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  simpa [hydrogenCount, mul_comm] using hsum

/-- The number of edges of a graph on `Fin n`, as a `Nat.card` of the edge set. -/
lemma natCard_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  simp [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset]

/-- **The carbon skeleton of an acyclic alkane is a tree with `n - 1` C–C bonds.**

Let `G` be the carbon skeleton of a connected saturated hydrocarbon with `n` carbon
atoms: a simple graph on `Fin n` in which every carbon has at most four bonds (the
remaining valences being filled by hydrogen, so that the molecule has
`hydrogenCount G = ∑ v, (4 - deg v)` hydrogen atoms).

Then the molecular formula is `CₙH₂ₙ₊₂` exactly when `G` is a tree, and in that case the
number of C–C bonds is `n - 1`. -/
theorem alkane_tree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 4) :
    hydrogenCount G = 2 * n + 2 ↔ (G.IsTree ∧ G.edgeFinset.card = n - 1) := by
  have hcount := hydrogenCount_add_twice_bonds G hdeg
  have htree : G.IsTree ↔ G.edgeFinset.card + 1 = n := by
    rw [SimpleGraph.isTree_iff_connected_and_card, natCard_edgeSet]
    simp [hconn]
  rw [htree]
  omega

/-- Sanity check (methane, `CH₄`): the one-carbon skeleton has no C–C bonds, is a tree,
and carries `4 = 2·1 + 2` hydrogens. -/
example : hydrogenCount (⊥ : SimpleGraph (Fin 1)) = 2 * 1 + 2 := by
  decide

end Chem

