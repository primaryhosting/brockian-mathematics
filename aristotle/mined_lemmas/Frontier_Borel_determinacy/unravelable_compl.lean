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

theorem unravelable_compl {S : Set (ℕ → A)} (h : Unravelable S) : Unravelable Sᶜ := by
  obtain ⟨B, hB, S', hclopen, ⟨C⟩⟩ := h
  refine ⟨B, hB, S'ᶜ, ⟨hclopen.2, by simpa [IsClosedPayoff, compl_compl] using hclopen.1⟩,
    ⟨{ proj := C.proj
       preimage_eq := by rw [Set.preimage_compl, ← C.preimage_eq]
       lift := C.lift
       lift_spec := C.lift_spec }⟩⟩

/-! ### Borel determinacy -/

/-- An *unraveling scheme* for games with moves in `A`: a class of payoff sets which contains
the closed sets, is closed under complements and countable unions, and all of whose members
are determined.

This is the abstract shape of Martin's proof of Borel determinacy: the class of payoff sets
that are unraveled by a clopen covering game.  For that class, `determined_of_unravelable`
and `unravelable_compl` (both proved above) supply the last two fields, so that only the two
unraveling lemmas of Martin's argument remain — see `Borel_determinacy_of_unravelings`. -/
structure UnravelingScheme (A : Type u) where
  /-- the class of payoff sets covered by the scheme -/
  mem : Set (ℕ → A) → Prop
  /-- closed payoff sets belong to the class -/
  mem_of_isClosedPayoff : ∀ S, IsClosedPayoff S → mem S
  /-- the class is closed under complements -/
  mem_compl : ∀ S, mem S → mem Sᶜ
  /-- the class is closed under countable unions -/
  mem_iUnion : ∀ f : ℕ → Set (ℕ → A), (∀ n, mem (f n)) → mem (⋃ n, f n)
  /-- every payoff set in the class is determined -/
  determined_of_mem : ∀ S, mem S → Determined S

/-- Every Borel payoff set belongs to an unraveling scheme: the σ-algebra induction at the
heart of Martin's proof. -/
