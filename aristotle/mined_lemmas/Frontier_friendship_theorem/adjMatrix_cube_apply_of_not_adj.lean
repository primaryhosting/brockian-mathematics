import RequestProject.Friendship
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

import Mathlib

/-!
# The friendship theorem (Erdős–Rényi–Sós)

If `G` is a finite graph in which every two distinct vertices have exactly one common
neighbour, then `G` has a vertex adjacent to all other vertices (a "politician").

The proof follows the classical argument:
* nonadjacent vertices have equal degrees (a length-3 walk count);
* hence a friendship graph with no politician is `d`-regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* the cases `d ≤ 2` are handled directly;
* for `d ≥ 3` we pick a prime `p ∣ d - 1` and compare two computations of the trace of
  `A ^ p`, where `A` is the adjacency matrix over `ZMod p`.
-/

namespace Frontier

open Finset SimpleGraph Matrix

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem adjMatrix_cube_apply_of_not_adj (hG : IsFriendship G) {v w : V} (h : ¬ G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = (G.degree v : R) := by
  have h3 : (G.adjMatrix R ^ 3 : Matrix V V R) = G.adjMatrix R * G.adjMatrix R ^ 2 := by
    rw [pow_succ']
  rw [h3, adjMatrix_mul_apply,
    Finset.sum_congr rfl (g := fun _ => (1 : R)) ?_]
  · rw [Finset.sum_const, ← card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
  · intro x hx
    rw [mem_neighborFinset] at hx
    exact adjMatrix_sq_apply_of_ne hG (by rintro rfl; exact h hx)

end Matrices

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
