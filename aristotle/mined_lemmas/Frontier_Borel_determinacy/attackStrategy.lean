import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

noncomputable def attackStrategy (A : Set (ℕ → X)) : Strategy X :=
  fun q => if h : ∃ a : X, ¬ IIWins A (q ++ [a]) then h.choose else Classical.arbitrary X

