import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

/-! ## Games on a set of moves

A play of the game is an infinite sequence `x : ℕ → A` of moves.  Player I plays the
moves `x 0, x 2, x 4, …` and player II plays the moves `x 1, x 3, x 5, …`.  Player I
wins the play `x` iff `x` belongs to the payoff set `S`.
-/

universe u

variable {A : Type u}

/-- The position (list of moves played) after the first `n` moves of the play `x`. -/

theorem isOpen_determinacy [TopologicalSpace A] [DiscreteTopology A] [Nonempty A]
    (S : Set (ℕ → A)) (hS : IsOpen S) : Det S :=
  seqOpen_determinacy S ((seqOpen_iff_isOpen S).2 hS)

/-! ## Coverings and unravelings (Martin) -/

/-- A *covering* of the game with moves in `A` by a game with moves in `B`: an
alphabet `B`, a length-preserving monotone map on positions inducing a map `π` on
plays, together with maps lifting strategies in the `B`-game to strategies in the
`A`-game so that every play following the lifted strategy is the image of a play
following the original one. -/
structure Covering (A : Type*) (B : Type*) where
  /-- the map on positions -/
  pmap : List B → List A
  pmap_length : ∀ q, (pmap q).length = q.length
  pmap_mono : ∀ q b, pmap q <+: pmap (q ++ [b])
  /-- the induced map on plays -/
  π : (ℕ → B) → (ℕ → A)
  π_spec : ∀ y n, pref (π y) n = pmap (pref y n)
  /-- lifting of strategies of player I -/
  liftI : (List B → B) → (List A → A)
  /-- lifting of strategies of player II -/
  liftII : (List B → B) → (List A → A)
  liftI_spec : ∀ σ x, FollowsI (liftI σ) x → ∃ y, FollowsI σ y ∧ π y = x
  liftII_spec : ∀ τ x, FollowsII (liftII τ) x → ∃ y, FollowsII τ y ∧ π y = x

/-- `S` is *unravelled* by a covering: there is a covering of the game by a game in
which the payoff set becomes clopen. -/
