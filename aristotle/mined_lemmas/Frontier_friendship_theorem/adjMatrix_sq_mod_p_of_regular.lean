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

theorem adjMatrix_sq_mod_p_of_regular (hG : IsFriendshipGraph G) (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG hd, dmod]

omit [DecidableEq V] in
