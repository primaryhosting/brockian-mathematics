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

lemma reachable_of_walk (h1 : ∀ h : H, M.degree (Sum.inr (α := C) h) = 1) :
    ∀ (n : ℕ) (c₁ c₂ : C) (p : M.Walk (Sum.inl c₁) (Sum.inl c₂)), p.length ≤ n →
      (carbonSkeleton M).Reachable c₁ c₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c₁ c₂ p hp
    cases p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons _ u _ hadj q =>
      match u, hadj, q with
      | Sum.inl c', hadj, q =>
        have hlen : q.length < n := by
          simp only [SimpleGraph.Walk.length_cons] at hp; omega
        have h1' : (carbonSkeleton M).Reachable c₁ c' :=
          SimpleGraph.Adj.reachable (by simpa [carbonSkeleton] using hadj)
        exact h1'.trans (ih q.length hlen c' c₂ q le_rfl)
      | Sum.inr hy, hadj, q =>
        match q with
        | SimpleGraph.Walk.cons (v := x) hadj' q' =>
          have huniq := SimpleGraph.degree_eq_one_iff_existsUnique_adj.1 (h1 hy)
          obtain ⟨w, _, hw⟩ := huniq
          have hx : x = Sum.inl c₁ := by
            rw [hw x hadj', ← hw (Sum.inl c₁) hadj.symm]
          subst hx
          have hlen : q'.length < n := by
            simp only [SimpleGraph.Walk.length_cons] at hp; omega
          exact ih q'.length hlen c₁ c₂ q' le_rfl

/-- The carbon skeleton of a connected molecule (with monovalent hydrogens) is preconnected. -/
