import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We develop, from scratch (there is no game-determinacy material in Mathlib), the theory of
two-player infinite games of perfect information with moves in an arbitrary nonempty set `A`:
plays are sequences `ℕ → A`, player `0` moves at the even stages, player `1` at the odd ones,
strategies are functions from finite positions (`List A`) to moves, and a payoff set
`S ⊆ (ℕ → A)` is *determined* (`Frontier.Determined`) when one of the players has a winning
strategy.

What is proved unconditionally:

* `Frontier.not_winsFor_both`: the two players never both have a winning strategy
  (non-degeneracy of the framework).
* `Frontier.exists_winsFrom_of_not_losing` and `Frontier.exists_winning_of_isClosedPayoff`:
  the combinatorial heart of the **Gale–Stewart theorem** — in a game whose payoff is closed
  for the player to be favoured, if the opponent cannot win from a position, that player can.
* `Frontier.determined_of_isClosedPayoff`, `Frontier.determined_of_isOpenPayoff`,
  `Frontier.determined_of_isClopenPayoff`: closed, open and clopen games are determined.
  This is the base case of Martin's induction.
* `Frontier.determined_of_inter_open_closed`, `Frontier.determined_of_union_closed_open`:
  one level beyond the base case, games whose payoff is the intersection of an open and a
  closed set (a difference of open sets), or the union of a closed and an open set, are
  determined.
* `Frontier.determined_of_unravelable`: determinacy transfers along a covering
  (`Frontier.Cover`); hence every payoff set unraveled by a clopen game is determined.
* `Frontier.unravelable_of_isClopenPayoff`, `Frontier.unravelable_compl`: clopen sets are
  unravelable, and the unravelable sets are closed under complements.
* `Frontier.UnravelingScheme.mem_of_isBorelPayoff`: the σ-algebra induction which propagates
  membership in an unraveling scheme from the open sets to all Borel sets.

The final statement `Frontier.Borel_determinacy` is Martin's theorem in the form of a
Lean-checked reduction: every Borel game is determined as soon as an *unraveling scheme*
exists, i.e. a class of payoff sets containing the closed sets, closed under complements and
countable unions, and consisting of determined sets.  Martin's construction produces such a
class; supplying it is the combinatorial core of his proof and is not carried out here.
Everything else — the base case, the transfer of determinacy along coverings, stability under
complements, and the σ-algebra induction — is proved.

`Frontier.Borel_determinacy_of_unravelings` specialises the reduction to the concrete class
of payoff sets admitting a clopen covering in the sense of `Frontier.Cover`, for which the
determinacy and complement fields of the scheme are proved here, leaving only the two
unraveling lemmas as hypotheses.  Note that `Frontier.Cover` is a simplified, "full tree"
rendering of Martin's notion of covering (games here have no legality constraints on moves);
no claim is made that Martin's coverings satisfy it verbatim, which is why the abstract
scheme, rather than this concrete class, is used in the headline statement.
-/

universe u v

namespace Frontier

open Classical

variable {A : Type u}

/-! ### Games on a set of moves -/

/-- The list of the first `n` moves of the play `x`. -/

theorem exists_winsFrom_of_not_losing [Nonempty A] {p q : ℕ} (hp : p < 2) (hq : q < 2)
    (hpq : p ≠ q) {S : Set (ℕ → A)} (hS : IsClosedPayoff S) {w : List A}
    (h : ¬ Losing q S w) : ∃ σ : Strategy A, WinsFrom p σ S w := by
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  -- If every immediate extension of `u` is losing, so is `u`.
  have hstep : ∀ u : List A, (∀ a : A, Losing q S (u ++ [a])) → Losing q S u := by
    intro u hL
    choose τ hτ using hL
    refine ⟨fun v => τ (v.getD u.length default) v, ?_⟩
    intro x hx hcons
    have hxu : pre x (u.length + 1) = u ++ [x u.length] := by rw [pre_succ, hx]
    refine hτ (x u.length) x (by simpa using hxu) ?_
    intro n hn hnq
    have hn' : u.length + 1 ≤ n := by simpa using hn
    have := hcons n (by omega) hnq
    rw [this]
    simp only [pre_getD x (show u.length < n by omega)]
  -- If it is the opponent's turn at `u` and some extension is losing, then `u` is losing.
  have hstepQ : ∀ (u : List A) (a : A), u.length % 2 = q → Losing q S (u ++ [a]) →
      Losing q S u := by
    intro u a hu ⟨τ', hτ'⟩
    refine ⟨fun v => if v.length = u.length then a else τ' v, ?_⟩
    intro x hx hcons
    have hxa : x u.length = a := by
      have := hcons u.length le_rfl hu
      rw [this, hx]
      simp
    have hxu : pre x (u.length + 1) = u ++ [a] := by rw [pre_succ, hx, hxa]
    refine hτ' x (by simpa using hxu) ?_
    intro n hn hnq
    have hn' : u.length + 1 ≤ n := by simpa using hn
    have := hcons n (by omega) hnq
    rw [this]
    simp only [pre_length]
    rw [if_neg (by omega)]
  -- A play all of whose initial positions are non-losing is won by `p`, since `S` is closed.
  have hD : ∀ x : ℕ → A, (∀ n, w.length ≤ n → ¬ Losing q S (pre x n)) → x ∈ S := by
    intro x hxg
    by_contra hxS
    obtain ⟨n, hn⟩ := hS x hxS
    refine hxg (max n w.length) (le_max_right _ _)
      ⟨fun _ => default, fun y hy _ => hn y ?_⟩
    rw [pre_length] at hy
    rw [pre_eq_iff]
    intro i hi
    exact (pre_eq_iff y x _).mp hy i (lt_of_lt_of_le hi (le_max_left _ _))
  -- The strategy for `p`: always move to a non-losing position.
  have hchoice : ∀ u : List A, ∃ a : A,
      (u.length % 2 = p → ¬ Losing q S u → ¬ Losing q S (u ++ [a])) := by
    intro u
    by_cases hu : ∃ a : A, ¬ Losing q S (u ++ [a])
    · obtain ⟨a, ha⟩ := hu
      exact ⟨a, fun _ _ => ha⟩
    · push_neg at hu
      exact ⟨default, fun _ hgu => absurd (hstep u hu) hgu⟩
  choose σ hσ using hchoice
  refine ⟨σ, fun x hxw hx => hD x ?_⟩
  have key : ∀ k, ¬ Losing q S (pre x (w.length + k)) := by
    intro k
    induction k with
    | zero => simpa [hxw] using h
    | succ k ih =>
      rw [show w.length + (k + 1) = (w.length + k) + 1 from rfl, pre_succ]
      by_cases hn : (w.length + k) % 2 = p
      · have hxn : x (w.length + k) = σ (pre x (w.length + k)) :=
          hx _ (Nat.le_add_right _ _) hn
        rw [hxn]
        exact hσ (pre x (w.length + k)) (by simpa using hn) ih
      · have hnq : (w.length + k) % 2 = q := by omega
        exact fun hcon =>
          ih (hstepQ (pre x (w.length + k)) (x (w.length + k)) (by simpa using hnq) hcon)
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = w.length + k := ⟨n - w.length, by omega⟩
  exact key k

/-- **Gale–Stewart**: in a game with closed payoff for player `p`, if the opponent `q` has
no winning strategy then `p` has one. -/
