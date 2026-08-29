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

theorem card_commonNeighbors_eq_one (hG : IsFriendshipGraph G) {v w : V} (hvw : v ≠ w) :
    #{u ∈ univ | G.Adj v u ∧ G.Adj u w} = 1 := by
  obtain ⟨u, hu, huniq⟩ := hG v w hvw
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · exact fun h => huniq x ⟨h.1, h.2.symm⟩
  · rintro rfl; exact ⟨hu.1, hu.2.symm⟩

variable {R : Type*} [Semiring R]

/-- Off-diagonal entries of the square of the adjacency matrix of a friendship graph are `1`:
there is exactly one walk of length two between two distinct vertices. -/
