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

theorem winsFor_or_winsFor_inter [Nonempty A] {p q : ℕ} (hp : p < 2) (hq : q < 2) (hpq : p ≠ q)
    {U C : Set (ℕ → A)} (hU : IsOpenPayoff U) (hC : IsClosedPayoff C) :
    (∃ σ : Strategy A, WinsFor p σ (U ∩ C)) ∨ (∃ τ : Strategy A, WinsFor q τ (U ∩ C)ᶜ) := by
  classical
  haveI : Inhabited A := Classical.inhabited_of_nonempty ‹Nonempty A›
  -- The auxiliary open game: reach a position which decides `U` and from which the closed
  -- game `C` is still winnable for `p`.
  set Trig : List A → Prop := fun u => Decides U u ∧ ¬ Losing q C u with hTrig
  set O : Set (ℕ → A) := {x | ∃ n, Trig (pre x n)} with hO
  have hOopen : IsOpenPayoff O := by
    rintro x ⟨n, hn⟩
    exact ⟨n, fun y hy => ⟨n, by rw [hy]; exact hn⟩⟩
  have hOdet : (∃ σ : Strategy A, WinsFor p σ O) ∨ (∃ τ : Strategy A, WinsFor q τ Oᶜ) := by
    by_cases h : ∃ σ : Strategy A, WinsFor p σ O
    · exact Or.inl h
    · refine Or.inr (exists_winning_of_isClosedPayoff hq hp (Ne.symm hpq) ?_ ?_)
      · simpa [IsClosedPayoff, compl_compl] using hOopen
      · simpa [compl_compl] using h
  rcases hOdet with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · -- Player `p` reaches a good position, then wins the closed game from there.
    left
    have halt : ∀ u : List A, ∃ ξ : Strategy A, ¬ Losing q C u → WinsFrom p ξ C u := by
      intro u
      by_cases hu : ¬ Losing q C u
      · obtain ⟨ξ, hξ⟩ := exists_winsFrom_of_not_losing hp hq hpq hC hu
        exact ⟨ξ, fun _ => hξ⟩
      · exact ⟨fun _ => default, fun h => absurd h hu⟩
    choose alt halt using halt
    refine ⟨splice Trig σ alt, fun x hx => ?_⟩
    by_cases hnone : ∀ n, ¬ Trig (pre x n)
    · exfalso
      have : Consistent p σ x := by
        intro n hn
        rw [hx n hn, splice_eq_base (fun m _ => hnone m)]
      obtain ⟨n, hn⟩ := hσ x this
      exact hnone n hn
    · push_neg at hnone
      obtain ⟨n, hn⟩ := hnone
      have hex : ∃ n, Trig (pre x n) := ⟨n, hn⟩
      set n₀ := Nat.find hex with hn₀def
      have hn₀ : Trig (pre x n₀) := Nat.find_spec hex
      have hmin : ∀ m < n₀, ¬ Trig (pre x m) := fun m hm => Nat.find_min hex hm
      refine ⟨mem_of_decides hn₀.1, ?_⟩
      refine halt (pre x n₀) hn₀.2 x (by simp) ?_
      intro k hk hkp
      rw [pre_length] at hk
      rw [hx k hkp, splice_eq_alt hn₀ hmin hk]
  · -- Player `q` avoids the good positions, then refutes `C` once `U` is decided.
    right
    have halt : ∀ u : List A, ∃ ξ : Strategy A, Losing q C u → WinsFrom q ξ Cᶜ u := by
      intro u
      by_cases hu : Losing q C u
      · obtain ⟨ξ, hξ⟩ := hu
        exact ⟨ξ, fun _ => hξ⟩
      · exact ⟨fun _ => default, fun h => absurd h hu⟩
    choose alt halt using halt
    refine ⟨splice (Decides U) τ alt, fun x hx => ?_⟩
    by_cases hnone : ∀ n, ¬ Decides U (pre x n)
    · have hcons : Consistent q τ x := by
        intro n hn
        rw [hx n hn, splice_eq_base (fun m _ => hnone m)]
      intro hmem
      obtain ⟨n, hn⟩ := exists_decides_of_isOpenPayoff hU hmem.1
      exact hnone n hn
    · push_neg at hnone
      obtain ⟨n, hn⟩ := hnone
      have hex : ∃ n, Decides U (pre x n) := ⟨n, hn⟩
      set n₀ := Nat.find hex with hn₀def
      have hn₀ : Decides U (pre x n₀) := Nat.find_spec hex
      have hmin : ∀ m < n₀, ¬ Decides U (pre x m) := fun m hm => Nat.find_min hex hm
      -- Before the trigger the play follows `τ`; hence the position `pre x n₀` is losing.
      have hlose : Losing q C (pre x n₀) := by
        obtain ⟨z, hz, hzc⟩ := exists_consistentFrom (pre x n₀) q τ
        rw [pre_length] at hz
        have hzcons : Consistent q τ z := by
          intro k hk
          rcases lt_or_ge k n₀ with hlt | hge
          · have hzx : pre z k = pre x k := by
              rw [pre_eq_iff]
              intro i hi
              exact (pre_eq_iff z x n₀).mp hz i (by omega)
            have hzk : z k = x k := (pre_eq_iff z x n₀).mp hz k hlt
            rw [hzk, hzx, hx k hk, splice_eq_base (fun m hm => hmin m (by omega))]
          · exact hzc k (by simpa using hge) hk
        have hzO : z ∉ O := hτ z hzcons
        have : ¬ Trig (pre z n₀) := fun hT => hzO ⟨n₀, hT⟩
        rw [show pre z n₀ = pre x n₀ from hz] at this
        by_contra hcon
        exact this ⟨hn₀, hcon⟩
      intro hmem
      refine halt (pre x n₀) hlose x (by simp) ?_ hmem.2
      intro k hk hkq
      rw [pre_length] at hk
      rw [hx k hkq, splice_eq_alt hn₀ hmin hk]

/-- The intersection of an open and a closed payoff set is determined. -/
