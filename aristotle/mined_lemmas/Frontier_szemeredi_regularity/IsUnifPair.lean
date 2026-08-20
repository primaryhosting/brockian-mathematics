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

def IsUnifPair (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) (s t : Finset α) : Prop :=
  ∀ s' ⊆ s, ∀ t' ⊆ t, (#s : ℝ) * ε ≤ #s' → (#t : ℝ) * ε ≤ #t' →
    |dens G s' t' - dens G s t| < ε

/-- `dens` agrees with Mathlib's rational-valued `SimpleGraph.edgeDensity`. -/
