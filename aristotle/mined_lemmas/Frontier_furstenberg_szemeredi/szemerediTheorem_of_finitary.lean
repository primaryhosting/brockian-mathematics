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

theorem szemerediTheorem_of_finitary (h : ∀ k, SzemerediFinitary k) : SzemerediTheorem :=
  fun _A k hA => furstenberg_szemeredi (h k) hA

/-- The base case: every set of positive upper density contains arithmetic progressions of
length at most `3`. -/
