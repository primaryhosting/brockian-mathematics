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

theorem vlevel_infinity (hκ : κ.IsInaccessible) :
    ∃ i : VLevel κ.ord, (∃ e, VMem κ.ord e i ∧ ∀ z, ¬ VMem κ.ord z e) ∧
      ∀ y, VMem κ.ord y i → ∃ s, VMem κ.ord s i ∧ ∀ z,
        VMem κ.ord z s ↔ (VMem κ.ord z y ∨ z = y) := by
  have homega : (Ordinal.omega0 : Ordinal.{u}) < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  refine ⟨⟨(Ordinal.omega0 : Ordinal.{u}).toZFSet, by
      rw [Ordinal.rank_toZFSet]; exact homega⟩, ⟨⟨∅, ?_⟩, ?_⟩, ?_⟩
  · rw [ZFSet.rank_empty]
    exact hκ.isRegular.ord_pos
  · refine ⟨?_, fun z hz => ZFSet.notMem_empty _ hz⟩
    rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro y hy
    rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff] at hy
    obtain ⟨a, ha, hay⟩ := hy
    have hsucc : Order.succ a < Ordinal.omega0 :=
      Ordinal.isSuccLimit_omega0.succ_lt ha
    refine ⟨⟨(Order.succ a).toZFSet, ?_⟩, ?_, fun z => ?_⟩
    · rw [Ordinal.rank_toZFSet]
      exact hsucc.trans homega
    · rw [VLevel.mem_iff, Ordinal.mem_toZFSet_iff]
      exact ⟨Order.succ a, hsucc, rfl⟩
    · rw [VLevel.mem_iff, Ordinal.toZFSet_succ, ZFSet.mem_insert_iff, VLevel.eq_iff, hay,
        VLevel.mem_iff]
      exact or_comm

