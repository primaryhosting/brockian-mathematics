import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma exists_bad_move [Inhabited A] {W : Set (ℕ → A)} {p : List A}
    (hp : Even p.length) (h : ¬ IWinsFrom W p) (a : A) :
    ∃ b, ¬ IWinsFrom W (p ++ [a, b]) := by
  by_contra hc
  push_neg at hc
  exact h (IWinsFrom_of_forall hp a hc)

/-- **Gale–Stewart theorem**: every open game is determined.

The game is played on a (nonempty, discrete) set of moves `A`; players I and II alternately
choose elements of `A`, player I moving at the even-numbered turns, producing a play
`f : ℕ → A`. Player I wins if the play belongs to the payoff set `W`, which is assumed open
in the product topology. The conclusion is that one of the two players has a winning strategy.
(The proof only uses that `W` is open, so it holds for any topology on `A`; the discreteness
assumption is the standard setting in which "open game" is meant.) -/
