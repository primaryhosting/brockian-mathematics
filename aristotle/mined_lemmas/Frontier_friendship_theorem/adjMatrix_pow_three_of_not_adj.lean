import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
  {d : ℕ}

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem adjMatrix_pow_three_of_not_adj (hG : UniqueCommonFriend G) (R : Type*) [Semiring R]
    {v w : V} (h : ¬ G.Adj v w) : (G.adjMatrix R ^ 3) v w = (G.degree v : R) := by
  have h3 : (G.adjMatrix R) ^ 3 = G.adjMatrix R * (G.adjMatrix R) ^ 2 := by rw [← pow_succ']
  rw [h3, adjMatrix_mul_apply]
  have : ∀ u ∈ G.neighborFinset v, ((G.adjMatrix R) ^ 2) u w = 1 := by
    intro u hu
    refine adjMatrix_sq_of_ne hG R ?_
    rintro rfl
    exact h (G.mem_neighborFinset v u |>.mp hu)
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree]

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
