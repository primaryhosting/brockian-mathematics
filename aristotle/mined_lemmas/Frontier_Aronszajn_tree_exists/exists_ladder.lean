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

theorem exists_ladder (a : Ordinal.{0}) (ha0 : a ≠ 0) (hcnt : (Set.Iio a).Countable)
    (hlim : ∀ b, b < a → Order.succ b < a) :
    ∃ al : ℕ → Ordinal.{0}, al 0 = 0 ∧ StrictMono al ∧ (∀ n, al n < a) ∧
      ∀ b, b < a → ∃ n, b < al n := by
  have hne : (Set.Iio a).Nonempty := ⟨0, pos_of_ne_zero ha0⟩
  obtain ⟨s, hs⟩ := hcnt.exists_eq_range hne
  set al : ℕ → Ordinal.{0} := fun n => Nat.rec (0 : Ordinal.{0})
    (fun n x => max (Order.succ x) (Order.succ (s n))) n with hal
  have halsucc : ∀ n, al (n + 1) = max (Order.succ (al n)) (Order.succ (s n)) := fun n => rfl
  have hsa : ∀ n, s n < a := by
    intro n
    have : s n ∈ Set.Iio a := by rw [hs]; exact ⟨n, rfl⟩
    exact this
  have hlt : ∀ n, al n < a := by
    intro n
    induction n with
    | zero => exact pos_of_ne_zero ha0
    | succ n ih =>
      rw [halsucc]
      exact max_lt (hlim _ ih) (hlim _ (hsa n))
  have hmono : StrictMono al := strictMono_nat_of_lt_succ (fun n => by
    rw [halsucc]
    exact lt_of_lt_of_le (Order.lt_succ (al n)) (le_max_left _ _))
  refine ⟨al, rfl, hmono, hlt, ?_⟩
  intro b hb
  have : b ∈ Set.range s := by rw [← hs]; exact hb
  obtain ⟨n, rfl⟩ := this
  exact ⟨n + 1, by rw [halsucc]; exact lt_of_lt_of_le (Order.lt_succ (s n)) (le_max_right _ _)⟩

/-- The invariant maintained along the `ω`-chain used at a limit stage: `f` is injective below
`al n` with infinite co-range, is a finite modification of `cf (al n)`, and avoids the finite
set `K`, which has at least `n` elements. -/
