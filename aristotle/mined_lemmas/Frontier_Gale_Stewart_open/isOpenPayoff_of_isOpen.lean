/-
/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
Every open game is determined (Gale–Stewart).

We consider the infinite two-player game on a nonempty set `A` of moves: the two players
alternately choose elements of `A`, player I moving at the even stages and player II at the odd
stages, producing a play `x : ℕ → A`.  Player I wins the play `x` iff `x ∈ W`, where `W` is the
payoff set.  A *strategy* is a function `List A → A` assigning a move to every position (finite
sequence of previous moves).

The theorem states: if `W` is open in the product topology on `ℕ → A` (with `A` discrete), then
either player I has a winning strategy or player II has one.
-/

namespace Frontier

open scoped Classical

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem isOpenPayoff_of_isOpen [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W) :
    IsOpenPayoff W := by
  intro x hx
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
  intro i hi
  have : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy i (by omega)]
  exact (hu i hi).2

/-- **Gale–Stewart theorem**: every open game is determined.

`A` is the (nonempty) set of moves, `W ⊆ A^ℕ` the payoff set of player I, open in the product
topology of the discrete topology on `A`.  Then either player I has a strategy `σ` all of whose
plays lie in `W`, or player II has a strategy `τ` all of whose plays avoid `W`.

(The discreteness assumption is stated because it is part of the classical statement; the proof
only uses that `W` is open in the product topology.) -/
