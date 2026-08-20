/-
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 does not permit a module docstring to precede `import`, so the header above is
-- wrapped in an outer block comment.)
import Mathlib

open Finset Filter MeasureTheory
open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that the set `A ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with positive common difference `d`. -/

def SzemerediTheorem : Prop :=
  ∀ (A : Set ℕ) (k : ℕ), 0 < upperDensity A → ContainsAP A k

section Density

variable {A : Set ℕ}

/-- A set of positive upper density has, for some `ε > 0`, infinitely many initial segments in
which it occupies at least an `ε`-fraction. -/
