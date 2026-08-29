import Mathlib
import RequestProject.Frontier

/-!
# Gale–Stewart for open games: the topological form

`RequestProject.Frontier` proves the Gale–Stewart theorem `Frontier.Gale_Stewart_open` with the
combinatorial formulation of openness (`Frontier.IsOpenPayoff`).  Here we check that this
hypothesis is exactly openness of the payoff set in the product topology on `ℕ → A` where `A`
carries the discrete topology, and record the resulting topological statement
`Frontier.Gale_Stewart_open_topological`.

(Discreteness of `A` is only needed for the converse implication
`Frontier.isOpen_of_isOpenPayoff`; openness for an arbitrary topology on `A` already implies the
combinatorial condition, hence determinacy.)
-/

namespace Frontier

universe u

variable {A : Type u} [TopologicalSpace A]

/-- An open set of the product topology on `ℕ → A` is an open payoff set. -/

theorem Gale_Stewart_open_topological [Inhabited A] (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : Strategy A, ∀ τ : Strategy A, play [] σ τ ∈ W) ∨
    (∃ τ : Strategy A, ∀ σ : Strategy A, play [] σ τ ∉ W) :=
  Gale_Stewart_open (fun x => x ∈ W) (isOpenPayoff_of_isOpen hW)

end Frontier

#print axioms Frontier.Gale_Stewart_open
#print axioms Frontier.Gale_Stewart_open_topological

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Gale–Stewart theorem for open games

We formalise the infinite two-player game on a nonempty type `A` of moves with payoff set
`W : (Nat → A) → Prop`.  Player I plays the moves with even index, Player II the moves with odd
index, and Player I wins a play `x : Nat → A` iff `W x`.

A *strategy* is a function `List A → A` assigning a move to every finite position (the list of
moves played so far, in chronological order).  Given a starting position `p` and strategies
`σ` (for I) and `τ` (for II), `Frontier.pos p σ τ k` is the position after `k` further moves and
`Frontier.play p σ τ : Nat → A` is the resulting infinite play.

`Frontier.IsOpenPayoff W` says that `W` is open in the product topology on `Nat → A` where `A`
carries the discrete topology: every winning play has a finite initial segment all of whose
extensions are winning.  (That this is literally equivalent to `IsOpen W` for the Mathlib product
topology is proved in `RequestProject.FrontierTopology`.)

The Gale–Stewart theorem `Frontier.Gale_Stewart_open` then states that an open game is
determined: one of the two players has a winning strategy.

This file is deliberately independent of Mathlib, so that the required header comment can be the
very first thing in the file.
-/

namespace Frontier

universe u

/-- A strategy: a move for every finite position (list of moves played so far). -/
abbrev Strategy (A : Type u) := List A → A

attribute [local instance 0] Classical.propDecidable

variable {A : Type u} [Inhabited A]

/-- `pos p σ τ k` is the position reached from the position `p` after `k` further moves, when
Player I follows `σ` and Player II follows `τ`.  Player I moves at positions of even length. -/
