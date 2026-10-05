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

theorem neighborFinset_eq_of_degree_eq_two [Nonempty V] (hG : IsFriendshipGraph G)
    (hd : G.IsRegularOfDegree 2) (v : V) : G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_neighborFinset] at hx
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
  · have hfr := card_of_regular hG hd
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ]
    have : G.degree v = 2 := hd v
    rw [card_neighborFinset_eq_degree, this]
    omega

/-- A `d`-regular friendship graph with `d ≤ 2` has a politician. -/
