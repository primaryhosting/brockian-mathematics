/-
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Frontier

variable {α : Type*}

/-- The edge density between two finsets of vertices `s` and `t` of a graph `G`: the number of
pairs `(x, y) ∈ s × t` with `x` adjacent to `y`, divided by `#s * #t`. -/

theorem dens_eq_edgeDensity (G : SimpleGraph α) [DecidableRel G.Adj] (s t : Finset α) :
    dens G s t = ((G.edgeDensity s t : ℚ) : ℝ) := by
  rw [dens, SimpleGraph.edgeDensity_def, ← SimpleGraph.interedges_def, Rat.cast_div]
  push_cast
  ring

/-- `IsUnifPair` agrees with Mathlib's `SimpleGraph.IsUniform` over `ℝ`. -/
