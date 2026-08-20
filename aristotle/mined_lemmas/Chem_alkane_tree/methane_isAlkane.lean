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

