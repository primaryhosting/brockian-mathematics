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

lemma exists_prefix_subset_of_isOpen [TopologicalSpace A] [DiscreteTopology A]
    {W : Set (ℕ → A)} (hW : IsOpen W) {x : ℕ → A} (hx : x ∈ W) :
    ∃ n, ∀ y : ℕ → A, (∀ i, i < n → y i = x i) → y ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW x hx
  refine ⟨(I.sup id) + 1, fun y hy => ?_⟩
  apply hsub
  intro a ha
  have h1 : (id a) ≤ I.sup id := Finset.le_sup ha
  simp only [id] at h1
  have hya : y a = x a := hy a (by omega)
  rw [hya]
  exact (hu a ha).2

/-- **The Gale–Stewart theorem**: every open game is determined.

Player I moves at the even indices, player II at the odd ones, and player I wins a play
`x : ℕ → A` iff `x ∈ W`.  If the payoff set `W` is open in the product topology (`A` being
discrete), then either player I has a winning strategy, or player II has one. -/
