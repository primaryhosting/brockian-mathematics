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

theorem isBorelPayoff_of_isOpen {A : Set (ℕ → X)} (hA : IsOpen A) : IsBorelPayoff A :=
  MeasurableSpace.measurableSet_generateFrom hA

/-- **Martin's theorem, as a statement**: every Borel game on `X` is determined. -/
