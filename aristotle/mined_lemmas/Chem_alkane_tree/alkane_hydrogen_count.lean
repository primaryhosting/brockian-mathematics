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

namespace Chem

/-- A model of an acyclic (saturated) alkane `CₙH₂ₙ₊₂`.

The atoms of the molecule are the elements of a (finite) type `V`, the covalent bonds are
the edges of a simple graph `G` on `V`, and `C` is the set of carbon atoms (so `Cᶜ` is the
set of hydrogen atoms).  The conditions say:

* there is at least one carbon atom;
* there are exactly `n` carbon atoms and exactly `2 * n + 2` hydrogen atoms;
* carbon is tetravalent (four bonds) and hydrogen is monovalent (one bond);
* the molecule is connected and acyclic, i.e. its bond graph is a tree.
-/
structure IsAlkane {V : Type*} (G : SimpleGraph V) (C : Set V) (n : ℕ) : Prop where
  /-- The molecule contains at least one carbon atom. -/
  pos_carbon : 0 < n
  /-- There are exactly `n` carbon atoms. -/
  card_carbon : C.ncard = n
  /-- There are exactly `2 * n + 2` hydrogen atoms. -/
  card_hydrogen : Cᶜ.ncard = 2 * n + 2
  /-- Carbon is tetravalent. -/
  carbon_valence : ∀ v ∈ C, (G.neighborSet v).ncard = 4
  /-- Hydrogen is monovalent. -/
  hydrogen_valence : ∀ v ∉ C, (G.neighborSet v).ncard = 1
  /-- The molecule is connected and contains no ring: its bond graph is a tree. -/
  tree : G.IsTree

/-- The carbon skeleton of a molecule: the graph induced on the set of carbon atoms,
whose edges are exactly the carbon–carbon bonds. -/
abbrev carbonSkeleton {V : Type*} (G : SimpleGraph V) (C : Set V) : SimpleGraph C :=
  G.induce C

/-- A monovalent atom has a subsingleton neighbourhood. -/

theorem alkane_hydrogen_count {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {C : Set V} [DecidablePred (· ∈ C)] {n h : ℕ}
    (hC : C.ncard = n) (hH : Cᶜ.ncard = h)
    (h4 : ∀ v ∈ C, (G.neighborSet v).ncard = 4)
    (h1 : ∀ v ∉ C, (G.neighborSet v).ncard = 1)
    (htree : G.IsTree) : h = 2 * n + 2 := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hsplit : ∑ v ∈ C.toFinset, G.degree v + ∑ v ∈ C.toFinsetᶜ, G.degree v
      = ∑ v : V, G.degree v := Finset.sum_add_sum_compl _ _
  have hn : C.toFinset.card = n := by rw [← hC, Set.ncard_eq_toFinset_card']
  have hh : C.toFinsetᶜ.card = h := by
    rw [← hH, Set.ncard_eq_toFinset_card', Set.toFinset_compl]
  have e1 : ∑ v ∈ C.toFinset, G.degree v = 4 * n := by
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [← ncard_neighborSet_eq_degree v, h4 v (by simpa using hv)])]
    simp [hn, mul_comm]
  have e2 : ∑ v ∈ C.toFinsetᶜ, G.degree v = h := by
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [← ncard_neighborSet_eq_degree v, h1 v (by simpa using hv)])]
    simp [hh]
  have hcard := htree.card_edgeFinset
  have hV : C.toFinset.card + C.toFinsetᶜ.card = Fintype.card V := Finset.card_add_card_compl _
  rw [e1, e2] at hsplit
  rw [← hsplit] at hsum
  omega

/-!
### Non-vacuity: methane `CH₄`

The hypotheses of `Chem.IsAlkane` are satisfiable: methane, whose bond graph is the star with
centre the carbon atom `0` and leaves the four hydrogen atoms `1, 2, 3, 4`, is an alkane
with `n = 1`.
-/

/-- The bond graph of methane: atom `0` is the carbon, atoms `1, 2, 3, 4` the hydrogens. -/
