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

theorem ReachWithin.reach {nbr : Fin n → Fin D → Fin n} {s t : Fin n} {k : ℕ}
    (h : ReachWithin nbr s t k) : Reach nbr s t := by
  obtain ⟨w, j, _, hw⟩ := h
  exact ⟨w, j, hw⟩

/-- Reachability along neighbour maps agrees with the reflexive-transitive closure of the
edge relation, i.e. with the usual notion of connectivity of the underlying graph. -/
