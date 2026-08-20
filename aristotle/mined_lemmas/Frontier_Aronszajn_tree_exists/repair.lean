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

theorem repair (a : Ordinal.{0}) (h : Ordinal → ℕ) (S : Set Ordinal) (K : Set ℕ)
    (hS : S.Finite) (hinj : Set.InjOn h (Set.Iio a \ S))
    (hK : Disjoint (h '' (Set.Iio a \ S)) K)
    (hinf : ((h '' (Set.Iio a \ S)) ∪ K)ᶜ.Infinite) :
    ∃ h' : Ordinal → ℕ, (∀ γ, γ ∉ S → h' γ = h γ) ∧ Set.InjOn h' (Set.Iio a) ∧
      Disjoint (h' '' Set.Iio a) K ∧ ((h' '' Set.Iio a)ᶜ).Infinite := by
  classical
  set C : Set ℕ := ((h '' (Set.Iio a \ S)) ∪ K)ᶜ with hCdef
  obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 hS.countable
  set e : ℕ ↪ C := hinf.natEmbedding _ with he
  set ι : Ordinal → ℕ := fun γ => (e (j γ) : ℕ) with hιdef
  have hιC : ∀ γ, ι γ ∈ C := fun γ => (e (j γ)).2
  have hιinj : Set.InjOn ι S := by
    intro x hx y hy hxy
    have : e (j x) = e (j y) := Subtype.ext hxy
    exact hj hx hy (e.injective this)
  set h' : Ordinal → ℕ := fun γ => if γ ∈ S then ι γ else h γ with hh'
  have hoff : ∀ γ, γ ∉ S → h' γ = h γ := fun γ hγ => if_neg hγ
  have hon : ∀ γ, γ ∈ S → h' γ = ι γ := fun γ hγ => if_pos hγ
  have himg : h' '' Set.Iio a ⊆ (h '' (Set.Iio a \ S)) ∪ ι '' S := by
    rintro v ⟨γ, hγ, rfl⟩
    by_cases hs : γ ∈ S
    · exact Or.inr ⟨γ, hs, (hon γ hs).symm ▸ rfl⟩
    · exact Or.inl ⟨γ, ⟨hγ, hs⟩, (hoff γ hs).symm ▸ rfl⟩
  refine ⟨h', hoff, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S
    · rw [hon x hxs, hon y hys] at hxy; exact hιinj hxs hys hxy
    · rw [hon x hxs, hoff y hys] at hxy
      have hc := hιC x
      rw [hxy] at hc
      have hmem : y ∈ Set.Iio a \ S := ⟨hy, hys⟩
      exact absurd (Set.mem_union_left K (Set.mem_image_of_mem h hmem)) hc
    · rw [hoff x hxs, hon y hys] at hxy
      have hc := hιC y
      rw [← hxy] at hc
      have hmem : x ∈ Set.Iio a \ S := ⟨hx, hxs⟩
      exact absurd (Set.mem_union_left K (Set.mem_image_of_mem h hmem)) hc
    · rw [hoff x hxs, hoff y hys] at hxy; exact hinj ⟨hx, hxs⟩ ⟨hy, hys⟩ hxy
  · rw [Set.disjoint_left]
    intro v hv hvK
    rcases himg hv with hv1 | ⟨γ, hγ, rfl⟩
    · exact (Set.disjoint_left.1 hK hv1) hvK
    · exact (hιC γ) (Or.inr hvK)
  · refine Set.Infinite.mono ?_ (hinf.diff (hS.image ι))
    intro v hv
    simp only [Set.mem_compl_iff]
    intro hv2
    rcases himg hv2 with h1 | h2
    · exact hv.1 (Or.inl h1)
    · exact hv.2 h2

/-! ### The coherent sequence -/

open Classical in
/-- A coherent sequence of almost injections, defined by transfinite recursion. -/
