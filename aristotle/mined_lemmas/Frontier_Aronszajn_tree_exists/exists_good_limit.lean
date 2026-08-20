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

theorem exists_good_limit (a : Ordinal.{0}) (ha : a < ω₁) (ha0 : a ≠ 0)
    (hlim : ∀ b, b < a → Order.succ b < a) (ih : ∀ b, b < a → Good b (cf b)) :
    ∃ E : Ordinal → ℕ, Good a E := by
  classical
  obtain ⟨al, hal0, hmono, hlta, hcof⟩ :=
    exists_ladder a ha0 (countable_Iio_of_lt_omega_one ha) hlim
  have hIio0 : Set.Iio (al 0) = (∅ : Set Ordinal) := by rw [hal0]; exact Iio_zero_ordinal
  have hinv0 : LimInv al 0 (fun _ => 0) ∅ := by
    refine ⟨?_, ?_, ?_, ?_, le_rfl⟩
    · rw [hIio0]; exact Set.injOn_empty _
    · rw [hIio0]; simpa using Set.infinite_univ
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγ, -⟩
      rw [hal0] at hγ
      exact absurd hγ (by simp)
    · simp
  have step : ∀ (n : ℕ) (p : (Ordinal → ℕ) × Finset ℕ), ∃ q : (Ordinal → ℕ) × Finset ℕ,
      LimInv al n p.1 p.2 → (LimInv al (n + 1) q.1 q.2 ∧ (∀ γ, γ < al n → q.1 γ = p.1 γ) ∧
        p.2 ⊆ q.2) := by
    intro n p
    by_cases hp : LimInv al n p.1 p.2
    · obtain ⟨f', K', h1, h2, h3⟩ := lim_step al a hlta hmono ih n p.1 p.2 hp
      exact ⟨(f', K'), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨p, fun hc => absurd hc hp⟩
  choose G hG using step
  set P : ℕ → (Ordinal → ℕ) × Finset ℕ :=
    fun n => Nat.rec ((fun _ => 0), (∅ : Finset ℕ)) (fun n p => G n p) n with hP
  have hPs : ∀ n, P (n + 1) = G n (P n) := fun n => rfl
  have hinvn : ∀ n, LimInv al n (P n).1 (P n).2 := by
    intro n
    induction n with
    | zero => exact hinv0
    | succ n ihn => rw [hPs]; exact (hG n (P n) ihn).1
  have hagree : ∀ n γ, γ < al n → (P (n + 1)).1 γ = (P n).1 γ := by
    intro n γ hγ
    rw [hPs]
    exact (hG n (P n) (hinvn n)).2.1 γ hγ
  have hKmono : ∀ n, (P n).2 ⊆ (P (n + 1)).2 := by
    intro n
    rw [hPs]
    exact (hG n (P n) (hinvn n)).2.2
  have hagree' : ∀ m n, m ≤ n → ∀ γ, γ < al m → (P n).1 γ = (P m).1 γ := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro γ _; rfl
    | succ n hn ihn =>
      intro γ hγ
      rw [hagree n γ (lt_of_lt_of_le hγ (hmono.monotone hn)), ihn γ hγ]
  have hKmono' : ∀ m n, m ≤ n → (P m).2 ⊆ (P n).2 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hn ihn => exact ihn.trans (hKmono n)
  set E : Ordinal → ℕ := fun γ => if h : ∃ n, γ < al n then (P (Nat.find h)).1 γ else 0 with hE
  have hEeq : ∀ n γ, γ < al n → E γ = (P n).1 γ := by
    intro n γ hγ
    have hex : ∃ n, γ < al n := ⟨n, hγ⟩
    have h0 : E γ = if h : ∃ n, γ < al n then (P (Nat.find h)).1 γ else 0 := rfl
    rw [h0, dif_pos hex]
    exact (hagree' (Nat.find hex) n (Nat.find_le hγ) γ (Nat.find_spec hex)).symm
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨n1, hn1⟩ := hcof x hx
    obtain ⟨n2, hn2⟩ := hcof y hy
    have hxN : x < al (max n1 n2) := lt_of_lt_of_le hn1 (hmono.monotone (le_max_left n1 n2))
    have hyN : y < al (max n1 n2) := lt_of_lt_of_le hn2 (hmono.monotone (le_max_right n1 n2))
    rw [hEeq _ x hxN, hEeq _ y hyN] at hxy
    exact (hinvn _).1 hxN hyN hxy
  · have hUsub : (⋃ n, (↑((P n).2) : Set ℕ)) ⊆ (E '' Set.Iio a)ᶜ := by
      intro v hv
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hv
      intro hcon
      obtain ⟨γ, hγ, hγv⟩ := hcon
      obtain ⟨m, hm⟩ := hcof γ hγ
      have hγN : γ < al (max m n) := lt_of_lt_of_le hm (hmono.monotone (le_max_left m n))
      have hmem : (P (max m n)).1 γ ∈ (P (max m n)).1 '' Set.Iio (al (max m n)) := ⟨γ, hγN, rfl⟩
      have hdis := (hinvn (max m n)).2.2.2.1
      refine (Set.disjoint_left.1 hdis hmem) ?_
      have hv2 : v = (P (max m n)).1 γ := by rw [← hγv, hEeq _ γ hγN]
      rw [← hv2]
      exact Finset.mem_coe.2 (hKmono' n (max m n) (le_max_right m n) (Finset.mem_coe.1 hn))
    refine Set.Infinite.mono hUsub ?_
    intro hfin
    have hcard : ∀ n, n ≤ hfin.toFinset.card := by
      intro n
      refine le_trans (hinvn n).2.2.2.2 (Finset.card_le_card ?_)
      intro x hx
      exact hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨n, Finset.mem_coe.2 hx⟩)
    exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
  · intro b hb
    obtain ⟨n, hn⟩ := hcof b hb
    have h1 : AEq b E (P n).1 := by
      refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγ, hne⟩
      exact absurd (hEeq n γ (hγ.trans hn)) hne
    have h2 : AEq b (P n).1 (cf (al n)) := (hinvn n).2.2.1.mono hn.le
    have h3 : AEq b (cf (al n)) (cf b) := (ih (al n) (hlta n)).2.2 b hn
    exact (h1.trans h2).trans h3

/-- Every countable stage of the coherent sequence has the required properties. -/
