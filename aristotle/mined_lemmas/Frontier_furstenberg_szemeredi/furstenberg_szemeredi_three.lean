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

theorem furstenberg_szemeredi_three {k : ℕ} (hk : k ≤ 3) {A : Set ℕ}
    (hA : 0 < upperDensity A) : ContainsAP A k :=
  furstenberg_szemeredi (szemerediFinitary_of_le_three hk) hA

/-- The base case `k = 2` of Furstenberg's multiple recurrence theorem: the Poincaré recurrence
theorem. For a measure-preserving map of a finite measure space and a set `E` of positive
measure there is some `n > 0` with `E ∩ T^[n]⁻¹ E` of positive measure. -/
