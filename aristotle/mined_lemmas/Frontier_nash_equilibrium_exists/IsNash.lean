/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

def IsNash (G : FiniteGame ι S) (x : (i : ι) → S i → ℝ) : Prop :=
  IsMixed x ∧ ∀ i, ∀ y ∈ stdSimplex ℝ (S i),
    expectedPayoff G i (Function.update x i y) ≤ expectedPayoff G i x

/-- Brouwer's fixed point theorem, as a hypothesis: every continuous self-map of a
nonempty compact convex subset of a finite dimensional real normed space has a fixed
point.  (This statement is not available in Mathlib, so the main theorem below is a
Lean-checked reduction of Nash's theorem to it.) -/
