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

def dig (D : ℕ) [NeZero D] (i j : ℕ) : Fin D :=
  ⟨i / D ^ j % D, Nat.mod_lt _ (Nat.pos_of_neZero D)⟩

/-- The branching program that, on a `D`-regular graph on `Fin n`, tries out all `D ^ k`
direction sequences of length `k` starting at `s`, and accepts if it ever meets `t`.
Its memory consists of a single vertex together with one Boolean flag. -/
