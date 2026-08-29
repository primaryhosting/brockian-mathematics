/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header above is a plain comment
-- and is repeated below as the module docstring.)
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A *friendship graph*: any two distinct vertices have exactly one common neighbour
("every two people have exactly one common friend"). -/

theorem adjMatrix_pow_three_apply_of_not_adj (hG : IsFriendshipGraph G) {v w : V}
    (hvw : ¬ G.Adj v w) : (G.adjMatrix R ^ 3 : Matrix V V R) v w = G.degree v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [adjMatrix_sq_apply_of_ne hG, Nat.cast_one]
  rintro rfl
  rw [mem_neighborFinset] at hx
  exact hvw hx

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
