import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's
lemma from the Lean core logic, using its own minimal set theory, because Lean forbids `import`
commands after the required header comment).  Here we state and prove the same results in terms of
Mathlib's `Set`, `IsChain`, `Preorder` and `PartialOrder`, via `exists_maximal_of_chains_bounded`
and `zorn_le`.
-/

namespace SetTheory

/-- **Zorn's lemma** for a preorder: if every chain has an upper bound, then there is a maximal
element `m`, i.e. every `a` with `m ≤ a` satisfies `a ≤ m`. -/
theorem zorn_preorder {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h le_trans

/-- **Zorn's lemma** for a partial order: if every chain has an upper bound, then there is a
maximal element `m`, i.e. every `a` with `m ≤ a` equals `m`. -/
theorem zorn_partialOrder {α : Type*} [PartialOrder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn_preorder h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩

/-- The same statement phrased with Mathlib's `IsMax`, deduced from `zorn_le`. -/
theorem zorn_isMax {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, IsMax m :=
  zorn_le fun c hc => let ⟨ub, hub⟩ := h c hc; ⟨ub, fun _ ha => hub _ ha⟩

end SetTheory

/-!
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained: Lean requires `import` commands to appear before any
module documentation, so in order for the header comment above to be the very first thing in the
file we develop everything (a minimal theory of sets, chains, and Hausdorff's maximality
principle) from the Lean core logic only.  The companion file `SetTheoryZornMathlib.lean` states
and proves the same theorem in terms of Mathlib's `Set` and `IsChain`.
-/

universe u

namespace SetTheory

variable {α : Type u}

/-! ### A minimal theory of sets -/

/-- A subset of `α`, encoded as a predicate. -/
def Set (α : Type u) : Type u := α → Prop

namespace Set

instance : Membership α (Set α) := ⟨fun s a => s a⟩

theorem mem_def {s : Set α} {a : α} : a ∈ s ↔ s a := Iff.rfl

/-- Inclusion of sets. -/
protected def Subset (s t : Set α) : Prop := ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : HasSubset (Set α) := ⟨Set.Subset⟩

theorem ext {s t : Set α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

protected theorem Subset.rfl {s : Set α} : s ⊆ s := fun _ ha => ha

protected theorem Subset.trans {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun _ ha => h₂ (h₁ ha)

protected theorem Subset.antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t :=
  ext fun _ => ⟨fun ha => h₁ ha, fun ha => h₂ ha⟩

theorem subset_of_eq {s t : Set α} (h : s = t) : s ⊆ t := h ▸ Subset.rfl

/-- The union of a family of sets. -/
def sUnion (S : Set (Set α)) : Set α := fun a => ∃ s, s ∈ S ∧ a ∈ s

theorem mem_sUnion {S : Set (Set α)} {a : α} : a ∈ sUnion S ↔ ∃ s, s ∈ S ∧ a ∈ s := Iff.rfl

theorem subset_sUnion_of_mem {S : Set (Set α)} {s : Set α} (h : s ∈ S) : s ⊆ sUnion S :=
  fun _ ha => ⟨s, h, ha⟩

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ s, s ∈ S → s ⊆ t) : sUnion S ⊆ t :=
  fun _ ha => match ha with | ⟨s, hs, has⟩ => h s hs has

/-- Insert an element into a set. -/
protected def insert (a : α) (s : Set α) : Set α := fun b => b = a ∨ b ∈ s

theorem mem_insert (a : α) (s : Set α) : a ∈ Set.insert a s := Or.inl rfl

theorem subset_insert (a : α) (s : Set α) : s ⊆ Set.insert a s := fun _ ha => Or.inr ha

end Set

open Set

/-! ### Chains -/

/-- A chain is a set whose elements are pairwise comparable for `r`. -/
def IsChain (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y ∨ r y x

/-- `SuperChain r s t` means that `t` is a chain strictly containing `s`. -/
def SuperChain (r : α → α → Prop) (s t : Set α) : Prop := IsChain r t ∧ s ⊆ t ∧ s ≠ t

/-- A chain `s` is maximal if no chain strictly contains it. -/
def IsMaxChain (r : α → α → Prop) (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

open Classical in
/-- If the chain `s` admits a strictly larger chain, then `SuccChain r s` is one such chain;
otherwise `SuccChain r s = s`. -/
noncomputable def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then Classical.choose h else s

variable {r : α → α → Prop} {s c c₁ c₂ : Set α}

theorem succChain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  classical
  have hs : IsChain r s ∧ SuperChain r s (Classical.choose h) := Classical.choose_spec h
  rw [SuccChain, dif_pos h]
  exact hs.2

theorem subset_succChain : s ⊆ SuccChain r s := by
  classical
  by_cases h : ∃ t, IsChain r s ∧ SuperChain r s t
  · exact (succChain_spec h).2.1
  · rw [SuccChain, dif_neg h]; exact Subset.rfl

theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) := by
  classical
  by_cases h : ∃ t, IsChain r s ∧ SuperChain r s t
  · exact (succChain_spec h).1
  · rw [SuccChain, dif_neg h]; exact hs

theorem IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
    SuperChain r s (SuccChain r s) := by
  have hex : ∃ t, IsChain r t ∧ s ⊆ t ∧ s ≠ t := by
    apply Classical.byContradiction
    intro hcon
    exact hs₂ ⟨hs₁, fun t ht hst =>
      Classical.byContradiction fun hne => hcon ⟨t, ht, hst, hne⟩⟩
  obtain ⟨t, ht, hst, hne⟩ := hex
  exact succChain_spec ⟨t, hs₁, ht, hst, hne⟩

theorem IsChain.insert (hs : IsChain r s) {a : α}
    (ha : ∀ b, b ∈ s → a ≠ b → r a b ∨ r b a) : IsChain r (Set.insert a s) := by
  intro x hx y hy hxy
  rcases hx with hx | hx
  · subst hx
    rcases hy with hy | hy
    · exact absurd hy.symm hxy
    · exact ha y hy hxy
  · rcases hy with hy | hy
    · subst hy
      exact (ha x hx (fun h => hxy h.symm)).symm
    · exact hs hx hy hxy

/-! ### Hausdorff's maximality principle -/

/-- Predicate for whether a set is reachable from `∅` using `SuccChain` and `sUnion`. -/
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure r s → ChainClosure r (SuccChain r s)
  | union : ∀ {S : Set (Set α)}, (∀ s, s ∈ S → ChainClosure r s) → ChainClosure r (sUnion S)

/-- An explicit maximal chain: the union of all sets in `ChainClosure`. -/
noncomputable def maxChain (r : α → α → Prop) : Set α := sUnion (fun s => ChainClosure r s)

theorem chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ hs => hs

private theorem chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : ∀ {c₃}, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) :
    SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    rcases ih with ih | ih
    · exact Or.inl (Subset.trans ih subset_succChain)
    · rcases h hc₃ ih with heq | hsub
      · exact Or.inl (subset_of_eq (congrArg (SuccChain r) heq))
      · exact Or.inr hsub
  | @union S _ ih =>
    by_cases hn : SuccChain r c₂ ⊆ sUnion S
    · exact Or.inl hn
    · refine Or.inr (sUnion_subset fun a ha => ?_)
      rcases ih a ha with h' | h'
      · exact absurd (Subset.trans h' (subset_sUnion_of_mem ha)) hn
      · exact h'

private theorem chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ ⊆ c₂) : c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ with
  | @succ c₃ hc₃ ih =>
    rcases chainClosure_succ_total_aux hc₁ (fun {c₄} hc₄ h₄ => ih hc₄ h₄) with h₁ | h₁
    · exact Or.inl (Subset.antisymm h₁ h)
    · rcases ih hc₁ h₁ with heq | h₂
      · exact Or.inr (subset_of_eq (congrArg (SuccChain r) heq.symm))
      · exact Or.inr (Subset.trans h₂ subset_succChain)
  | @union S hS ih =>
    by_cases hsub : sUnion S ⊆ c₁
    · exact Or.inl (Subset.antisymm hsub h)
    · refine Or.inr ?_
      have hex : ∃ c₃, c₃ ∈ S ∧ ¬ c₃ ⊆ c₁ := by
        apply Classical.byContradiction
        intro hcon
        exact hsub (sUnion_subset fun t ht =>
          Classical.byContradiction fun hnt => hcon ⟨t, ht, hnt⟩)
      obtain ⟨c₃, hc₃, h₁⟩ := hex
      apply Classical.byContradiction
      intro h₂
      rcases chainClosure_succ_total_aux hc₁ (fun {c₄} hc₄ h₄ => ih c₃ hc₃ hc₄ h₄) with hx | hx
      · exact h₁ (Subset.trans subset_succChain hx)
      · rcases ih c₃ hc₃ hc₁ hx with hy | hy
        · exact h₁ (subset_of_eq hy)
        · exact h₂ (Subset.trans hy (subset_sUnion_of_mem hc₃))

theorem ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) :
    c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ := by
  rcases chainClosure_succ_total_aux hc₂ (fun {c₃} hc₃ h₃ => chainClosure_succ_total hc₃ hc₁ h₃)
    with h | h
  · exact Or.inl (Subset.trans subset_succChain h)
  · exact Or.inr h

theorem ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (hc : SuccChain r c₂ = c₂) : c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    rcases chainClosure_succ_total hc₃ hc₂ ih with heq | hsub
    · exact heq ▸ subset_of_eq hc
    · exact hsub
  | union _ ih => exact sUnion_subset ih

theorem ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) :
    SuccChain r c = c ↔ c = maxChain r := by
  constructor
  · intro h
    exact Subset.antisymm (subset_sUnion_of_mem hc)
      (ChainClosure.succ_fixpoint chainClosure_maxChain hc h)
  · intro h
    refine Subset.antisymm ?_ subset_succChain
    exact Subset.trans (subset_sUnion_of_mem hc.succ) (subset_of_eq h.symm)

theorem ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ ih => exact ih.succ
  | @union S hS ih =>
    intro x hx y hy hxy
    obtain ⟨t₁, ht₁, hx₁⟩ := hx
    obtain ⟨t₂, ht₂, hy₂⟩ := hy
    rcases ChainClosure.total (hS _ ht₁) (hS _ ht₂) with ht | ht
    · exact ih t₂ ht₂ (ht hx₁) hy₂ hxy
    · exact ih t₁ ht₁ hx₁ (ht hy₂) hxy

/-- **Hausdorff's maximality principle**: `maxChain r` is a maximal chain. -/
theorem maxChain_spec : IsMaxChain r (maxChain r) := by
  apply Classical.byContradiction
  intro h
  have hsuper := chainClosure_maxChain.isChain.superChain_succChain h
  exact hsuper.2.2 (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm

/-! ### Zorn's lemma -/

/-- **Zorn's lemma** for an arbitrary transitive relation: if every chain has an upper bound,
then there is a maximal element. -/
theorem exists_maximal_of_chains_bounded
    (h : ∀ c : Set α, IsChain r c → ∃ ub, ∀ a, a ∈ c → r a ub)
    (trans : ∀ {a b c : α}, r a b → r b c → r a c) : ∃ m, ∀ a, r m a → r a m := by
  obtain ⟨ub, hub⟩ := h (maxChain r) maxChain_spec.1
  refine ⟨ub, fun a ha => ?_⟩
  have hchain : IsChain r (Set.insert a (maxChain r)) :=
    maxChain_spec.1.insert fun b hb _ => Or.inr (trans (hub b hb) ha)
  have heq : maxChain r = Set.insert a (maxChain r) :=
    maxChain_spec.2 hchain (subset_insert _ _)
  exact hub a (heq ▸ Set.mem_insert a (maxChain r))

/-- **Zorn's lemma**: in a preorder in which every chain has an upper bound, there is a maximal
element `m`, i.e. every `a` with `m ≤ a` also satisfies `a ≤ m`. -/
theorem zorn {α : Type u} [LE α] (le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a, a ∈ c → a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h le_trans

end SetTheory

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

