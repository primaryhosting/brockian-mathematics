import RequestProject.Coherent

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has
no uncountable branch (equivalently, no uncountable chain).

We formalize a tree as a partial order `T` together with a rank function `rk : T → Ordinal`
whose fibres are the levels; see `Frontier.IsAronszajnTree`.  The main result is
`Frontier.Aronszajn_tree_exists`.
-/

open Ordinal Cardinal Set
open scoped Ordinal

namespace Frontier

/-- `rk` exhibits the partial order `T` as an Aronszajn tree:

* every node has rank a countable ordinal, and the rank strictly increases along the order;
* the set of predecessors of a node is a chain, and contains exactly one element of each
  rank below the rank of the node (so `T` is a tree and `rk` is the height function);
* every level `α < ω₁` is nonempty (the tree has height exactly `ω₁`) and countable;
* every chain (in particular every branch) of `T` is countable.
-/
structure IsAronszajnTree {T : Type 1} [PartialOrder T] (rk : T → Ordinal.{0}) : Prop where
  /-- Every node has countable rank. -/
  rk_lt_omega_one : ∀ t : T, rk t < ω₁
  /-- The rank increases strictly along the order. -/
  rk_mono : ∀ s t : T, s < t → rk s < rk t
  /-- The predecessors of a node form a chain. -/
  pred_chain : ∀ s₁ s₂ t : T, s₁ < t → s₂ < t → s₁ ≤ s₂ ∨ s₂ ≤ s₁
  /-- Every rank below the rank of `t` is realized by a predecessor of `t`. -/
  pred_exists : ∀ t : T, ∀ γ < rk t, ∃ s : T, s < t ∧ rk s = γ
  /-- The tree has height `ω₁`: all levels below `ω₁` are nonempty. -/
  level_nonempty : ∀ α < ω₁, ∃ t : T, rk t = α
  /-- All levels are countable. -/
  level_countable : ∀ α : Ordinal.{0}, {t : T | rk t = α}.Countable
  /-- There is no uncountable chain, in particular no uncountable branch. -/
  chain_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

/-- Truncation of a function at an ordinal. -/

theorem exists_good_succ (b : Ordinal.{0}) (hb : Good b (cf b)) :
    ∃ E : Ordinal → ℕ, Good (Order.succ b) E := by
  have hset : Set.Iio (Order.succ b) \ {b} = Set.Iio b := by
    ext x
    simp only [Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff, Order.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
    · intro h; exact ⟨h.le, ne_of_lt h⟩
  obtain ⟨hinj, hinf, hcoh⟩ := hb
  obtain ⟨E, hEoff, hEinj, -, hEinf⟩ :=
    repair (Order.succ b) (cf b) {b} ∅ (Set.finite_singleton b)
      (by rw [hset]; exact hinj) (by simp)
      (by rw [hset]; simpa using hinf)
  refine ⟨E, hEinj, hEinf, ?_⟩
  intro c hc
  have hcb : c ≤ b := Order.lt_succ_iff.1 hc
  have h1 : AEq c E (cf b) := by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro γ ⟨hγ, hne⟩
    exact absurd (hEoff γ (by simp; exact ne_of_lt (lt_of_lt_of_le hγ hcb))) hne
  refine h1.trans ?_
  rcases lt_or_eq_of_le hcb with h | h
  · exact hcoh c h
  · subst h; exact AEq.refl _ _

/-! ### The limit stage -/

/-- A countable limit ordinal is the supremum of a strictly increasing `ω`-sequence. -/
