-- (Lean requires `import` to be the first command of a file, so the header comment
-- follows it.)
import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalise Dijkstra's algorithm on a finite directed graph whose edge weights are
nonnegative (encoded by taking values in `ℝ≥0∞`, where `⊤` means "no edge"), and prove
that it computes the true shortest-path distances from a fixed source.
-/

namespace CS

open scoped ENNReal

variable {V : Type*}

/-! ## Walks, their weights, and the shortest-path distance -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

def endp (s : V) : List V → V
  | [] => s
  | v :: l => endp v l

/-- The total weight of the walk starting at `s` and visiting the vertices of `l` in order. -/
