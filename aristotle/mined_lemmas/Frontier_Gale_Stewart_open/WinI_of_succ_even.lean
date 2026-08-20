import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
# The Gale–Stewart theorem: open games are determined

We consider the infinite two-player game on a nonempty set of moves `A`.  A play is a
sequence `x : ℕ → A`; player I chooses the moves at even indices, player II the moves at
odd indices.  Player I wins the play `x` if `x ∈ W`, otherwise player II wins.

A *strategy* is a function `List A → A`, taking the history of the play so far (as a list,
in chronological order) to the next move.  Given a starting position `p : List A` and
strategies `σ` (for I) and `τ` (for II), the resulting play is `play p σ τ`.

The Gale–Stewart theorem states that if `W` is open (in the product topology, `A` being
discrete), then the game is determined: one of the two players has a winning strategy.
-/

variable {A : Type*}

/-- The history of the play after `n` further moves, starting from the position `p`,
when player I follows `σ` and player II follows `τ`.  The player to move at a position
`l` is player I if `l.length` is even and player II if `l.length` is odd. -/

lemma WinI_of_succ_even {p : List A} (hp : Even p.length) {a : A}
    (h : WinI W (p ++ [a])) : WinI W p := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun l => if l = p then a else σ l, fun τ => ?_⟩
  have key : ∀ n, hist p (fun l => if l = p then a else σ l) τ (n + 1) = hist (p ++ [a]) σ τ n := by
    intro n
    induction n with
    | zero => simp [hist_succ, hp]
    | succ n ih =>
      rw [hist_succ, ih, hist_succ]
      have hlen : (hist (p ++ [a]) σ τ n).length = p.length + 1 + n := by
        rw [hist_length]; simp
      have hne : hist (p ++ [a]) σ τ n ≠ p := by
        intro hcon
        rw [hcon] at hlen; omega
      simp [hne]
  rw [play_eq_of_hist_eq (by simp) key]
  exact hσ τ

/-- If it is player II's turn at `p` and player I wins from every successor position,
then player I wins from `p`. -/
