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
lemma degree_eq_sum_ite (v : C ⊕ H) :
    M.degree v = ∑ w : C ⊕ H, if M.Adj v w then 1 else 0 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]

/-- The degree of a carbon splits into its C–C bonds and its C–H bonds. -/
lemma carbon_degree_split (c : C) :
    M.degree (Sum.inl c) =
      (carbonSkeleton M).degree c + ∑ h : H, if M.Adj (Sum.inl c) (Sum.inr h) then 1 else 0 := by
  rw [degree_eq_sum_ite, Fintype.sum_sum_type]
  congr 1
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
  rfl

variable {M}

/-- A hydrogen without H–H bonds and of valence one has exactly one C–H bond. -/
lemma hydrogen_bond_count {h : H} (hval : M.degree (Sum.inr (α := C) h) = 1)
    (hHH : ∀ h₁ h₂ : H, ¬ M.Adj (Sum.inr h₁) (Sum.inr h₂)) :
    ∑ c : C, (if M.Adj (Sum.inl c) (Sum.inr h) then 1 else 0) = 1 := by
  have hsplit := degree_eq_sum_ite M (Sum.inr h)
  rw [Fintype.sum_sum_type] at hsplit
  have h2 : ∑ h' : H, (if M.Adj (Sum.inr h) (Sum.inr h') then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h' _
    simp [hHH h h']
  rw [h2, add_zero, hval] at hsplit
  have hcomm : ∑ c : C, (if M.Adj (Sum.inl c) (Sum.inr h) then 1 else 0)
      = ∑ c : C, (if M.Adj (Sum.inr h) (Sum.inl c) then 1 else 0) :=
    Finset.sum_congr rfl fun c _ => if_congr (SimpleGraph.adj_comm M _ _) rfl rfl
  rw [hcomm, ← hsplit]

/-- Degree counting: `4 * n = 2 * e + |H|`, where `n` is the number of carbons and `e` the
number of C–C bonds. -/
lemma four_mul_card_carbon (h4 : ∀ c : C, M.degree (Sum.inl c) = 4)
    (h1 : ∀ h : H, M.degree (Sum.inr (α := C) h) = 1)
    (hHH : ∀ h₁ h₂ : H, ¬ M.Adj (Sum.inr h₁) (Sum.inr h₂)) :
    4 * Fintype.card C =
      2 * (carbonSkeleton M).edgeFinset.card + Fintype.card H := by
  have key : ∑ c : C, M.degree (Sum.inl c)
      = (∑ c : C, (carbonSkeleton M).degree c)
        + ∑ c : C, ∑ h : H, (if M.Adj (Sum.inl c) (Sum.inr h) then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => carbon_degree_split M c
  rw [Finset.sum_congr rfl (fun c _ => h4 c), Finset.sum_const, smul_eq_mul,
    SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_comm] at key
  rw [Finset.sum_congr rfl (fun h _ => hydrogen_bond_count (h1 h) hHH), Finset.sum_const,
    smul_eq_mul] at key
  simpa [mul_comm] using key

end

section

variable {M : SimpleGraph (C ⊕ H)} [DecidableRel M.Adj]

/-- A walk in the molecule between two carbon atoms yields a path in the carbon skeleton:
a hydrogen atom, having degree one, can never be an interior vertex of a walk. -/
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
lemma carbonSkeleton_preconnected (hconn : M.Connected)
    (h1 : ∀ h : H, M.degree (Sum.inr (α := C) h) = 1) :
    (carbonSkeleton M).Preconnected := by
  intro c₁ c₂
  obtain ⟨p⟩ := hconn.preconnected (Sum.inl c₁) (Sum.inl c₂)
  exact reachable_of_walk h1 p.length c₁ c₂ p le_rfl

end

section

variable {M : SimpleGraph (C ⊕ H)} [DecidableRel M.Adj]

/-- **The carbon skeleton of a saturated hydrocarbon `CₙH₂ₙ₊₂` is a tree with `n - 1` C–C
bonds.**  Acyclicity is not assumed here: it is part of the conclusion. -/
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
theorem alkane_tree (hM : IsAlkane M) :
    (carbonSkeleton M).IsTree ∧
      (carbonSkeleton M).edgeFinset.card = Fintype.card C - 1 := by
  obtain ⟨htree, hcard⟩ := carbonSkeleton_isTree_and_card_edges hM.toIsSaturatedHydrocarbon
  exact ⟨htree, by omega⟩

/-- Conversely, for a connected molecule with tetravalent carbons, monovalent hydrogens and no
H–H bonds, having an acyclic carbon skeleton forces the molecular formula `CₙH₂ₙ₊₂`. -/
theorem card_hydrogen_of_carbonSkeleton_isTree
    (h4 : ∀ c : C, M.degree (Sum.inl c) = 4)
    (h1 : ∀ h : H, M.degree (Sum.inr (α := C) h) = 1)
    (hHH : ∀ h₁ h₂ : H, ¬ M.Adj (Sum.inr h₁) (Sum.inr h₂))
    (htree : (carbonSkeleton M).IsTree) :
    Fintype.card H = 2 * Fintype.card C + 2 := by
  have hcount := four_mul_card_carbon h4 h1 hHH
  have hcard := htree.card_edgeFinset
  omega

end

/-! ### Non-vacuity: methane `CH₄` is an alkane -/

namespace Methane

/-- Methane `CH₄`: one carbon bonded to four hydrogens. -/
def M : SimpleGraph (Unit ⊕ Fin 4) where
  Adj u v := u.isLeft ≠ v.isLeft
  symm := fun {_ _} h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel M.Adj := fun u v => inferInstanceAs (Decidable (u.isLeft ≠ v.isLeft))

lemma M_adj (u v : Unit ⊕ Fin 4) : M.Adj u v ↔ u.isLeft ≠ v.isLeft := Iff.rfl

lemma M_connected : M.Connected := by
  have hr : ∀ v : Unit ⊕ Fin 4, M.Reachable (Sum.inl ()) v := by
    intro v
    cases v with
    | inl u => cases u; exact SimpleGraph.Reachable.refl _
    | inr i => exact SimpleGraph.Adj.reachable (by simp [M_adj])
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma M_acyclic : M.IsAcyclic := by
  have h : M.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨M_connected, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  exact h.IsAcyclic

/-- Methane is an alkane, so the hypotheses of `Chem.IsAlkane` are not vacuous. -/
theorem isAlkane : Chem.IsAlkane M where
  carbon_valence := by decide
  hydrogen_valence := by intro i; fin_cases i <;> decide
  no_HH_bond := by decide
  connected := M_connected
  formula := by decide
  acyclic := M_acyclic

end Methane

end Chem

