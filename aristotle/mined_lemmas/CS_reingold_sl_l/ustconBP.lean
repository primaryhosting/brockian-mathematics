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

def ustconBP (n D k : ℕ) [NeZero D] (s t : Fin n) : BP (Fin n × Fin D) (Fin n) (Fin n × Bool) where
  length := D ^ k * k
  start := (s, decide (s = t))
  query := fun l p => (p.1, dig D (l / k) (l % k))
  next := fun l p a => (if (l + 1) % k = 0 then s else a, p.2 || decide (a = t))
  accept := fun p => p.2

