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

theorem szemerediFinitary_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediFinitary k :=
  szemerediFinitary_mono hk szemerediFinitary_three

/-- **Szemerédi's theorem**, in the form of a Lean-checked reduction of the infinitary
(positive upper density) statement to the finitary one, which in the ergodic-theoretic
approach of Furstenberg is supplied by the multiple recurrence theorem.

For `k ≤ 3` the hypothesis is unconditionally available
(see `Frontier.szemerediFinitary_of_le_three`), so the conclusion holds outright; this is the
base case of the induction on the length `k` of the progression. -/
