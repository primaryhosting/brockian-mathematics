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

theorem walk_congr (nbr : Fin n → Fin D → Fin n) (v : Fin n) (w w' : ℕ → Fin D) (j : ℕ)
    (h : ∀ x < j, w x = w' x) : walk nbr v w j = walk nbr v w' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [walk, ih (fun x hx => h x (by omega)), h j (by omega)]

