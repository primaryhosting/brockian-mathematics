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

def idCovering (A : Type u) : Covering A A where
  pmap := id
  pmap_length := fun _ => rfl
  pmap_mono := fun _ b => ⟨[b], rfl⟩
  π := id
  π_spec := fun _ _ => rfl
  liftI := id
  liftII := id
  liftI_spec := fun _ x hx => ⟨x, hx, rfl⟩
  liftII_spec := fun _ x hx => ⟨x, hx, rfl⟩

