/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

We formalize infinite two-player games with perfect information on a set `A` of moves.

A *play* is an element of `ℕ → A`. Player I chooses the moves with even index, Player II the
moves with odd index. A *strategy* for either player is a function `List A → A` assigning a
move to each position (a finite list of moves played so far, in order). The payoff set
`W : Set (ℕ → A)` is the set of plays won by Player I.

`gsPos σ τ p n` is the position reached after `n` further moves when the play starts from
position `p` and the players follow `σ` (Player I) and `τ` (Player II); `gsRun σ τ p` is the
resulting infinite play.

The main theorem `Frontier.Gale_Stewart_open` states the Gale–Stewart theorem: if the payoff
set `W` is open (for the product topology on `ℕ → A` with `A` discrete) then the game is
determined, i.e. one of the two players has a winning strategy.
-/

namespace Frontier

variable {A : Type*}

/-- The position reached after `n` moves starting from position `p`, when Player I follows the
strategy `σ` and Player II follows the strategy `τ`.  The player to move at a position `q` is
Player I if `q.length` is even and Player II otherwise. -/

lemma gsRun_shift [Nonempty A] {σ τ : List A → A} {p : List A} {a : A}
    (h : (if Even p.length then σ p else τ p) = a) :
    gsRun σ τ p = gsRun σ τ (p ++ [a]) := by
  funext n
  have h1 : n < (gsPos σ τ p (n + 2)).length := by rw [gsPos_length]; omega
  have h2 : (gsPos σ τ p (n + 2)).getD n (Classical.arbitrary A) = gsRun σ τ p n :=
    gsPos_getD_eq_run σ τ p h1
  rw [← h2, gsPos_shift h (n + 1)]
  exact gsPos_getD_eq_run σ τ (p ++ [a]) (by rw [gsPos_length]; simp; omega)

/-! ### The key combinatorial steps -/

/-- If Player I is to move at `p` and some move leads to a position won by Player I, then
Player I wins from `p`. -/
