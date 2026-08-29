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

theorem adjMatrix_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) {R : Type*} [Semiring R] :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x y
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast, of_apply]

omit [DecidableEq V] in
