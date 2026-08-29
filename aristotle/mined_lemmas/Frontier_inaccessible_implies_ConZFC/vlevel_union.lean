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

theorem vlevel_union (hκ : κ.IsInaccessible) :
    ∀ x : VLevel κ.ord, ∃ u : VLevel κ.ord, ∀ z,
      VMem κ.ord z u ↔ ∃ y, VMem κ.ord y x ∧ VMem κ.ord z y := by
  intro x
  refine ⟨⟨⋃₀ x.1, lt_of_le_of_lt (ZFSet.rank_sUnion_le x.1) x.2⟩, fun z => ?_⟩
  rw [VLevel.mem_iff, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨⟨y, VLevel.rank_lt_of_mem hyx⟩, hyx, hzy⟩
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨y.1, hyx, hzy⟩

