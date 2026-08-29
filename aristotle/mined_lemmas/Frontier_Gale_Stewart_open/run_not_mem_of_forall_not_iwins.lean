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

lemma run_not_mem_of_forall_not_iwins [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    {W : Set (ℕ → A)} (hW : IsOpen W) {σ τ : List A → A}
    (h : ∀ n, ¬ IWins W (gsPos σ τ [] n)) : gsRun σ τ [] ∉ W := by
  intro hmem
  set x := gsRun σ τ [] with hx
  -- openness gives a finite prefix of `x` all of whose extensions lie in `W`
  obtain ⟨n, hn⟩ : ∃ n, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W := by
    rw [isOpen_pi_iff] at hW
    obtain ⟨I, u, hu, hsub⟩ := hW x hmem
    refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
    intro i hi
    have h1 : i ≤ I.sup id := by simpa using Finset.le_sup (f := id) hi
    have : y i = x i := hy i (by omega)
    rw [this]
    exact (hu i hi).2
  set q := gsPos σ τ [] n with hq
  have hqlen : q.length = n := by rw [hq, gsPos_length]; simp
  refine h n ⟨fun _ => Classical.arbitrary A, fun τ' => ?_⟩
  refine hn _ (fun i hi => ?_)
  have h1 : gsRun (fun _ => Classical.arbitrary A) τ' q i = q.getD i (Classical.arbitrary A) :=
    gsRun_eq_of_lt _ _ _ (by omega)
  have h2 : q.getD i (Classical.arbitrary A) = x i :=
    gsPos_getD_eq_run σ τ [] (by rw [gsPos_length]; simpa using hi)
  rw [h1, h2]

/-! ### The Gale–Stewart theorem -/

/-- **Gale–Stewart theorem**: every open game is determined.

The moves are taken from a nonempty set `A` carrying the discrete topology, and the set `W` of
plays winning for Player I is open in the product topology on `ℕ → A`.  Positions are finite
lists of moves; Player I moves at positions of even length and Player II at positions of odd
length; `gsRun σ τ []` is the play resulting from the strategies `σ` (Player I) and `τ`
(Player II).  The conclusion is that either Player I has a strategy forcing the play into `W`,
or Player II has a strategy forcing the play outside `W`. -/
