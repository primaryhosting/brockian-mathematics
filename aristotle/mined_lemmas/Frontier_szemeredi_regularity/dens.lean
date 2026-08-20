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

noncomputable def dens (G : SimpleGraph α) [DecidableRel G.Adj] (s t : Finset α) : ℝ :=
  (#{p ∈ s ×ˢ t | G.Adj p.1 p.2} : ℝ) / ((#s : ℝ) * (#t : ℝ))

/-- A pair of finsets of vertices `(s, t)` is `ε`-uniform (`ε`-regular) in `G` when the edge
density between any pair of sufficiently large subsets `s' ⊆ s`, `t' ⊆ t` is within `ε` of the
edge density between `s` and `t`. -/
