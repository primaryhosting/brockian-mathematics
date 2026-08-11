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
lemma neighborSet_subsingleton_of_ncard_eq_one {V : Type*} {G : SimpleGraph V} {v : V}
    (h : (G.neighborSet v).ncard = 1) : (G.neighborSet v).Subsingleton := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
  rw [ha]
  exact Set.subsingleton_singleton

/-- The carbon skeleton of an alkane is connected: since every hydrogen atom is monovalent,
no path between two carbon atoms can pass through a hydrogen atom. -/
lemma IsAlkane.carbonSkeleton_connected {V : Type*} {G : SimpleGraph V} {C : Set V} {n : ℕ}
    (h : IsAlkane G C n) : (carbonSkeleton G C).Connected := by
  have hne : C.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h.card_carbon]; have := h.pos_carbon; omega)
  haveI := hne.to_subtype
  exact ⟨h.tree.isConnected.preconnected.induce_of_degree_eq_one
    fun v hv => neighborSet_subsingleton_of_ncard_eq_one (h.hydrogen_valence v hv)⟩

/-- **The carbon skeleton of an acyclic alkane `CₙH₂ₙ₊₂` is a tree with `n - 1` C–C bonds.** -/
theorem alkane_tree {V : Type*} [Finite V] {G : SimpleGraph V} {C : Set V} {n : ℕ}
    (h : IsAlkane G C n) :
    (carbonSkeleton G C).IsTree ∧ Nat.card (carbonSkeleton G C).edgeSet = n - 1 := by
  have htree : (carbonSkeleton G C).IsTree :=
    ⟨h.carbonSkeleton_connected, h.tree.IsAcyclic.induce C⟩
  refine ⟨htree, ?_⟩
  have := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  simp only [Nat.card_coe_set_eq, h.card_carbon] at this ⊢
  omega

/-- The number of neighbours of a vertex, as a `Set.ncard`, is its degree. -/
lemma ncard_neighborSet_eq_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) : (G.neighborSet v).ncard = G.degree v := by
  rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset]
  rfl

/-- **The molecular formula `CₙH₂ₙ₊₂` is forced.**  If the bond graph of a molecule is a tree
in which every carbon atom is tetravalent and every hydrogen atom is monovalent, and there are
`n` carbon atoms and `h` hydrogen atoms, then `h = 2 * n + 2`. -/
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
def methane : SimpleGraph (Fin 5) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := by rintro a b ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨by rintro a ⟨h, -⟩; exact h rfl⟩

instance : DecidableRel methane.Adj := fun a b => by
  unfold methane; dsimp; infer_instance

/-- The carbon atom of methane. -/
def methaneCarbon : Set (Fin 5) := {0}

lemma methane_isTree : methane.IsTree := by
  have hconn : methane.Connected := by
    have key : ∀ v : Fin 5, methane.Reachable 0 v := by
      intro v
      by_cases h : v = 0
      · subst h; rfl
      · exact SimpleGraph.Adj.reachable (⟨fun hh => h hh.symm, Or.inl rfl⟩ : methane.Adj 0 v)
    exact ⟨fun u v => ((key u).symm).trans (key v)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- Methane is an alkane with one carbon atom. -/
theorem methane_isAlkane : IsAlkane methane methaneCarbon 1 where
  pos_carbon := Nat.one_pos
  card_carbon := Set.ncard_singleton _
  card_hydrogen := by
    have : (methaneCarbonᶜ : Set (Fin 5)) = ↑({1, 2, 3, 4} : Finset (Fin 5)) := by
      ext x; fin_cases x <;> simp [methaneCarbon]
    rw [this, Set.ncard_coe_finset]
    decide
  carbon_valence := by
    intro v hv
    rw [show v = 0 from hv, ← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset]
    decide
  hydrogen_valence := by
    intro v hv
    have hv0 : v ≠ 0 := fun h => hv (by simp [methaneCarbon, h])
    clear hv
    rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset]
    revert hv0; revert v; decide
  tree := methane_isTree

/-- The carbon skeleton of methane is a tree with no C–C bond. -/
example : (carbonSkeleton methane methaneCarbon).IsTree ∧
    Nat.card (carbonSkeleton methane methaneCarbon).edgeSet = 0 :=
  alkane_tree methane_isAlkane

end Chem

