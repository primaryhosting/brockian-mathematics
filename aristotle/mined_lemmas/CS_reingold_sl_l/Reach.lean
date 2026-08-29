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

def Reach (nbr : Fin n → Fin D → Fin n) (s t : Fin n) : Prop :=
  ∃ w : ℕ → Fin D, ∃ j : ℕ, walk nbr s w j = t

/-- `t` is reachable from `s` by a walk of length at most `k`. -/
