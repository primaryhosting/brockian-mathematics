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

theorem isUnifPair_iff (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) (s t : Finset α) :
    IsUnifPair G ε s t ↔ G.IsUniform ε s t := by
  simp only [IsUnifPair, SimpleGraph.IsUniform, dens_eq_edgeDensity]

open scoped Classical in
/-- **Szemerédi's Regularity Lemma**.

For every `ε > 0` and every `l`, there is a bound `M`, depending only on `ε` and `l` (and not on
the graph nor on the number of vertices), such that every finite graph `G` on at least `l`
vertices admits a partition of its vertex set into between `l` and `M` nonempty parts which is
* an *equipartition*: any two parts have sizes differing by at most one, and
* `ε`-*regular*: the number of ordered pairs of distinct parts `(A, B)` that fail to be
  `ε`-uniform is at most `ε * (number of parts)²`. -/
