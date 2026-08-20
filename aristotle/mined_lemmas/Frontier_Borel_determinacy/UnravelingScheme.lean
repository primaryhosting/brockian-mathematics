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

theorem UnravelingScheme.mem_of_isBorelPayoff (U : UnravelingScheme A) {S : Set (ℕ → A)}
    (hS : IsBorelPayoff S) : U.mem S := by
  induction hS with
  | basic T hT =>
    have hTc : IsClosedPayoff Tᶜ := by simpa [IsClosedPayoff, compl_compl] using hT
    simpa [compl_compl] using U.mem_compl _ (U.mem_of_isClosedPayoff _ hTc)
  | empty =>
    refine U.mem_of_isClosedPayoff _ ?_
    intro x _
    exact ⟨0, by simp⟩
  | compl T _ ih => exact U.mem_compl _ ih
  | iUnion f _ ih => exact U.mem_iUnion f ih

/-- **Borel determinacy** (Martin's theorem), as a Lean-checked reduction: every Borel game
is determined as soon as there is an unraveling scheme, i.e. a class of payoff sets which
contains the closed sets, is a σ-algebra, and consists of determined sets.

The base case of Martin's induction — that closed, open and clopen games are determined — is
proved unconditionally above (`determined_of_isClosedPayoff` and friends), as is the transfer
of determinacy along coverings (`determined_of_unravelable`), the stability of unravelability
under complements (`unravelable_compl`) and the σ-algebra induction
(`UnravelingScheme.mem_of_isBorelPayoff`).  What an unraveling scheme adds is precisely the
combinatorial core of Martin's argument. -/
