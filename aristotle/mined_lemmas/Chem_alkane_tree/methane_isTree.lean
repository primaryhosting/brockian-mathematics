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
