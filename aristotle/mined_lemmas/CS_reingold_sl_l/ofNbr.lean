/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

def ofNbr (nbr : Fin n → Fin D → Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => ∃ e, nbr u e = v)

/-- For an undirected neighbour map (every edge can be traversed backwards), reachability
along the neighbour map is exactly connectivity in the underlying simple graph. -/
