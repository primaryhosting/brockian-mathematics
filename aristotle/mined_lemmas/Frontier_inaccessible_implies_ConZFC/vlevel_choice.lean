/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

universe u

namespace Frontier

open Cardinal Ordinal ZFSet Order

/-- The axioms of ZFC, stated for an arbitrary membership relation `mem` on a type `M`.

Separation and Replacement are stated in their *second-order* (schematic over all
ambient predicates/functions) form, which implies every first-order instance. -/
structure IsZFCModel {M : Type*} (mem : M → M → Prop) : Prop where
  /-- Extensionality. -/
  extensionality : ∀ x y : M, (∀ z, mem z x ↔ mem z y) → x = y
  /-- Foundation (regularity). -/
  foundation : ∀ x : M, (∃ z, mem z x) → ∃ y, mem y x ∧ ∀ z, mem z y → ¬ mem z x
  /-- Existence of the empty set. -/
  empty : ∃ e : M, ∀ z, ¬ mem z e
  /-- Pairing. -/
  pairing : ∀ x y : M, ∃ p : M, ∀ z, mem z p ↔ (z = x ∨ z = y)
  /-- Union. -/
  union : ∀ x : M, ∃ u : M, ∀ z, mem z u ↔ ∃ y, mem y x ∧ mem z y
  /-- Power set. -/
  powerset : ∀ x : M, ∃ p : M, ∀ z, mem z p ↔ ∀ w, mem w z → mem w x
  /-- Infinity: there is a set containing the empty set and closed under `y ↦ y ∪ {y}`. -/
  infinity : ∃ i : M, (∃ e, mem e i ∧ ∀ z, ¬ mem z e) ∧
      ∀ y, mem y i → ∃ s, mem s i ∧ ∀ z, mem z s ↔ (mem z y ∨ z = y)
  /-- Separation. -/
  separation : ∀ (P : M → Prop) (x : M), ∃ y : M, ∀ z, mem z y ↔ (mem z x ∧ P z)
  /-- Replacement. -/
  replacement : ∀ (F : M → M) (x : M), ∃ y : M, ∀ z, mem z y ↔ ∃ w, mem w x ∧ z = F w
  /-- Choice: every set of pairwise disjoint nonempty sets has a transversal. -/
  choice : ∀ x : M, (∀ y, mem y x → ∃ z, mem z y) →
      (∀ y y', mem y x → mem y' x → y ≠ y' → ∀ z, ¬(mem z y ∧ mem z y')) →
      ∃ c : M, ∀ y, mem y x → ∃ z, mem z y ∧ mem z c ∧ ∀ z', mem z' y → mem z' c → z' = z

/-- The `o`-th level of the von Neumann hierarchy, as a type. -/

theorem vlevel_choice (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, (∀ y, VMem κ.ord y x → ∃ z, VMem κ.ord z y) →
      (∀ y y', VMem κ.ord y x → VMem κ.ord y' x → y ≠ y' →
        ∀ z, ¬(VMem κ.ord z y ∧ VMem κ.ord z y')) →
      ∃ c : VLevel κ.ord, ∀ y, VMem κ.ord y x → ∃ z,
        VMem κ.ord z y ∧ VMem κ.ord z c ∧ ∀ z', VMem κ.ord z' y → VMem κ.ord z' c → z' = z := by
  intro x hne hdisj
  classical
  have hsel : ∀ w : (x.1 : Type (u + 1)), ∃ t : ZFSet.{u}, t ∈ w.1 := by
    intro w
    obtain ⟨z, hz⟩ := hne ⟨w.1, VLevel.rank_lt_of_mem w.2⟩ w.2
    exact ⟨z.1, hz⟩
  set e := equivShrink.{u} (x.1 : Type (u + 1)) with he
  set g : Shrink.{u} (x.1 : Type (u + 1)) → ZFSet.{u} := fun i => (hsel (e.symm i)).choose with hgdef
  have hgmem : ∀ i, g i ∈ (e.symm i).1 := fun i => (hsel (e.symm i)).choose_spec
  have hgrank : ∀ i, (g i).rank < κ.ord := fun i =>
    VLevel.rank_lt_of_mem (b := ⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩) (hgmem i)
  refine ⟨⟨ZFSet.range g, rank_range_lt hκ x.2 g hgrank⟩, fun y hy => ?_⟩
  have hy' : y.1 ∈ x.1 := hy
  refine ⟨⟨g (e ⟨y.1, hy'⟩), hgrank _⟩, ?_, ?_, ?_⟩
  · have h1 := hgmem (e ⟨y.1, hy'⟩)
    rwa [Equiv.symm_apply_apply] at h1
  · rw [VLevel.mem_iff, ZFSet.mem_range]
    exact ⟨_, rfl⟩
  · rintro z' hz'y hz'c
    rw [VLevel.mem_iff, ZFSet.mem_range] at hz'c
    obtain ⟨i, hi⟩ := hz'c
    have hz'mem : z'.1 ∈ (e.symm i).1 := hi ▸ hgmem i
    have hxmem : (e.symm i).1 ∈ x.1 := (e.symm i).2
    have hyy' : y = (⟨(e.symm i).1, VLevel.rank_lt_of_mem (e.symm i).2⟩ : VLevel κ.ord) := by
      by_contra hne'
      exact hdisj y _ hy hxmem hne' z' ⟨hz'y, hz'mem⟩
    have hsymm : e.symm i = ⟨y.1, hy'⟩ := Subtype.ext (congrArg Subtype.val hyy'.symm)
    have hie : i = e ⟨y.1, hy'⟩ := by rw [← hsymm, Equiv.apply_symm_apply]
    apply VLevel.ext
    rw [← hi, hie]

/-- **If `κ` is inaccessible then `V_κ` is a model of ZFC.** -/
