/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)
import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting three elements.
A `node i j l r` compares the elements sitting at positions `i` and `j` of the input and
branches accordingly; a `leaf p` outputs the permutation `p`. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving DecidableEq

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem sortTree3_correct (σ : Equiv.Perm (Fin 3)) : sortTree3.run σ = σ := by
  revert σ
  decide

/-- The tree `sortTree3` uses exactly 3 comparisons in the worst case. -/
