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

/-!
# The carbon skeleton of an acyclic alkane is a tree

A molecule is modelled as a finite simple graph `M` on the vertex type `C ⊕ H`, where `C` is
the (finite) set of carbon atoms and `H` the (finite) set of hydrogen atoms; edges are covalent
bonds.  Being a *saturated hydrocarbon of formula* `CₙH₂ₙ₊₂` is expressed by:

* every carbon is tetravalent (`M.degree (Sum.inl c) = 4`);
* every hydrogen is monovalent (`M.degree (Sum.inr h) = 1`);
* there are no H–H bonds;
* the molecule is connected;
* `|H| = 2 * |C| + 2`.

The *carbon skeleton* is the induced graph on the carbon atoms, `M.comap Sum.inl`.

The main result `Chem.alkane_tree` states that the carbon skeleton of an acyclic alkane
`CₙH₂ₙ₊₂` is a tree with exactly `n - 1` C–C bonds.
-/

namespace Chem

variable {C H : Type*} [Fintype C] [Fintype H]

/-- The carbon skeleton of a molecule graph on `C ⊕ H`: the graph induced on the carbon atoms,
whose edges are exactly the C–C bonds. -/
abbrev carbonSkeleton (M : SimpleGraph (C ⊕ H)) : SimpleGraph C := M.comap Sum.inl

/-- A *saturated hydrocarbon with molecular formula* `CₙH₂ₙ₊₂`, modelled as a finite simple
graph on carbon atoms `C` and hydrogen atoms `H`: carbons are tetravalent, hydrogens are
monovalent, there are no H–H bonds, the molecule is connected, and there are `2 * |C| + 2`
hydrogens. -/
structure IsSaturatedHydrocarbon (M : SimpleGraph (C ⊕ H)) [DecidableRel M.Adj] : Prop where
  /-- Carbon is tetravalent. -/
  carbon_valence : ∀ c : C, M.degree (Sum.inl c) = 4
  /-- Hydrogen is monovalent. -/
  hydrogen_valence : ∀ h : H, M.degree (Sum.inr h) = 1
  /-- There are no hydrogen–hydrogen bonds. -/
  no_HH_bond : ∀ h₁ h₂ : H, ¬ M.Adj (Sum.inr h₁) (Sum.inr h₂)
  /-- The molecule is connected. -/
  connected : M.Connected
  /-- The molecular formula is `CₙH₂ₙ₊₂`. -/
  formula : Fintype.card H = 2 * Fintype.card C + 2

/-- An *alkane*: an acyclic saturated hydrocarbon `CₙH₂ₙ₊₂`. -/
structure IsAlkane (M : SimpleGraph (C ⊕ H)) [DecidableRel M.Adj] : Prop
    extends IsSaturatedHydrocarbon M where
  /-- The molecule contains no ring. -/
  acyclic : M.IsAcyclic

section

variable (M : SimpleGraph (C ⊕ H)) [DecidableRel M.Adj]

/-- The degree of a vertex, written as a sum of indicators. -/

theorem carbonSkeleton_isTree_and_card_edges (hM : IsSaturatedHydrocarbon M) :
    (carbonSkeleton M).IsTree ∧
      (carbonSkeleton M).edgeFinset.card + 1 = Fintype.card C := by
  have hcount := four_mul_card_carbon hM.carbon_valence hM.hydrogen_valence hM.no_HH_bond
  rw [hM.formula] at hcount
  have hcard : (carbonSkeleton M).edgeFinset.card + 1 = Fintype.card C := by omega
  have hne : Nonempty C := by
    rw [← Fintype.card_pos_iff]; omega
  have htree : (carbonSkeleton M).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨⟨carbonSkeleton_preconnected hM.connected hM.hydrogen_valence⟩, ?_⟩
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card]
  exact ⟨htree, hcard⟩

/-- **The carbon skeleton of an acyclic alkane `CₙH₂ₙ₊₂` is a tree with `n - 1` C–C bonds.**

The hypothesis that the molecule is acyclic is included because the statement speaks of an
*acyclic* alkane; the proof does not need it, since acyclicity of the carbon skeleton already
follows from the molecular formula `CₙH₂ₙ₊₂` together with connectedness and the valences
(see `Chem.carbonSkeleton_isTree_and_card_edges`). -/
