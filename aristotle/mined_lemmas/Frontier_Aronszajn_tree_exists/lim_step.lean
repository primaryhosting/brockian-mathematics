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

theorem lim_step (al : ℕ → Ordinal.{0}) (a : Ordinal.{0}) (hlta : ∀ n, al n < a)
    (hmono : StrictMono al) (ih : ∀ b, b < a → Good b (cf b))
    (n : ℕ) (f : Ordinal → ℕ) (K : Finset ℕ) (hinv : LimInv al n f K) :
    ∃ (f' : Ordinal → ℕ) (K' : Finset ℕ), LimInv al (n + 1) f' K' ∧
      (∀ γ, γ < al n → f' γ = f γ) ∧ K ⊆ K' := by
  classical
  obtain ⟨hfinj, hfinf, hfaeq, hfdisj, hfcard⟩ := hinv
  set A := al n with hA
  set B := al (n + 1) with hB
  have hAB : A < B := hmono (Nat.lt_succ_self n)
  obtain ⟨hginj, hginf, hgcoh⟩ := ih B (hlta (n + 1))
  set g := cf B with hg
  have hfg : AEq A f g := hfaeq.trans (hgcoh A hAB).symm
  set D : Set Ordinal := {γ | γ < A ∧ f γ ≠ g γ} with hD
  have hDfin : D.Finite := hfg
  set hfun : Ordinal → ℕ := fun γ => if γ < A then f γ else g γ with hhfun
  have hfun_lt : ∀ γ, γ < A → hfun γ = f γ := fun γ h => if_pos h
  have hfun_ge : ∀ γ, A ≤ γ → hfun γ = g γ := fun γ h => if_neg (not_lt.2 h)
  set S : Set Ordinal := {γ | A ≤ γ ∧ γ < B ∧ (g γ ∈ f '' D ∨ g γ ∈ (↑K : Set ℕ))} with hS
  have hSfin : S.Finite := by
    have hginjS : Set.InjOn g S := fun x hx y hy hxy => hginj hx.2.1 hy.2.1 hxy
    refine Set.Finite.of_finite_image ?_ hginjS
    refine Set.Finite.subset ((hDfin.image f).union K.finite_toSet) ?_
    rintro v ⟨γ, hγ, rfl⟩
    exact hγ.2.2
  have hinj' : Set.InjOn hfun (Set.Iio B \ S) := by
    intro x hx y hy hxy
    rcases lt_or_ge x A with hxA | hxA <;> rcases lt_or_ge y A with hyA | hyA
    · rw [hfun_lt x hxA, hfun_lt y hyA] at hxy
      exact hfinj hxA hyA hxy
    · rw [hfun_lt x hxA, hfun_ge y hyA] at hxy
      by_cases hxD : x ∈ D
      · exact absurd (⟨hyA, hy.1, Or.inl ⟨x, hxD, hxy⟩⟩ : y ∈ S) hy.2
      · have hfx : f x = g x := by by_contra hc; exact hxD ⟨hxA, hc⟩
        rw [hfx] at hxy
        exact hginj (hxA.trans hAB) hy.1 hxy
    · rw [hfun_ge x hxA, hfun_lt y hyA] at hxy
      by_cases hyD : y ∈ D
      · exact absurd (⟨hxA, hx.1, Or.inl ⟨y, hyD, hxy.symm⟩⟩ : x ∈ S) hx.2
      · have hfy : f y = g y := by by_contra hc; exact hyD ⟨hyA, hc⟩
        rw [hfy] at hxy
        exact hginj hx.1 (hyA.trans hAB) hxy
    · rw [hfun_ge x hxA, hfun_ge y hyA] at hxy
      exact hginj hx.1 hy.1 hxy
  have hdisj' : Disjoint (hfun '' (Set.Iio B \ S)) (↑K : Set ℕ) := by
    rw [Set.disjoint_left]
    rintro v ⟨γ, hγ, rfl⟩ hvK
    rcases lt_or_ge γ A with h | h
    · rw [hfun_lt γ h] at hvK
      exact (Set.disjoint_left.1 hfdisj (Set.mem_image_of_mem f h)) hvK
    · rw [hfun_ge γ h] at hvK
      exact hγ.2 ⟨h, hγ.1, Or.inr hvK⟩
  have hsub : hfun '' (Set.Iio B \ S) ⊆ (g '' Set.Iio B) ∪ f '' D := by
    rintro v ⟨γ, hγ, rfl⟩
    rcases lt_or_ge γ A with h | h
    · rw [hfun_lt γ h]
      by_cases hd : γ ∈ D
      · exact Or.inr ⟨γ, hd, rfl⟩
      · have hfe : f γ = g γ := by by_contra hc; exact hd ⟨h, hc⟩
        rw [hfe]; exact Or.inl ⟨γ, h.trans hAB, rfl⟩
    · rw [hfun_ge γ h]; exact Or.inl ⟨γ, hγ.1, rfl⟩
  have hinf' : ((hfun '' (Set.Iio B \ S)) ∪ (↑K : Set ℕ))ᶜ.Infinite := by
    refine Set.Infinite.mono ?_ (hginf.diff ((hDfin.image f).union K.finite_toSet))
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_union]
    rintro (h1 | h2)
    · rcases hsub h1 with h | h
      · exact hv.1 h
      · exact hv.2 (Or.inl h)
    · exact hv.2 (Or.inr h2)
  obtain ⟨f', hf'off, hf'inj, hf'disj, hf'inf⟩ := repair B hfun S (↑K) hSfin hinj' hdisj' hinf'
  obtain ⟨k, hk⟩ := (hf'inf.diff K.finite_toSet).nonempty
  have hkK : k ∉ K := fun hc => hk.2 (Finset.mem_coe.2 hc)
  refine ⟨f', insert k K, ⟨hf'inj, hf'inf, ?_, ?_, ?_⟩, ?_, Finset.subset_insert k K⟩
  · refine Set.Finite.subset (hDfin.union hSfin) ?_
    rintro γ ⟨hγB, hne⟩
    by_cases hs : γ ∈ S
    · exact Or.inr hs
    · rw [hf'off γ hs] at hne
      rcases lt_or_ge γ A with h | h
      · rw [hfun_lt γ h] at hne; exact Or.inl ⟨h, hne⟩
      · rw [hfun_ge γ h] at hne; exact absurd rfl hne
  · rw [Finset.coe_insert, Set.disjoint_insert_right]
    exact ⟨hk.1, hf'disj⟩
  · rw [Finset.card_insert_of_notMem hkK]
    omega
  · intro γ hγ
    have hnS : γ ∉ S := fun hc => absurd hc.1 (not_le.2 hγ)
    rw [hf'off γ hnS, hfun_lt γ hγ]

/-- The limit stage. -/
