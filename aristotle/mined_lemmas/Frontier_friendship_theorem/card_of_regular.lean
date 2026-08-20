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

theorem card_of_regular [Nonempty V] (hG : IsFriendship G) (hd : G.IsRegularOfDegree d) :
    d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  have hsq := adjMatrix_sq_of_regular (R := ℕ) hG hd
  have h1 : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d + (Fintype.card V - 1) := by
    rw [hsq, ← Finset.add_sum_erase _ _ (mem_univ v)]
    simp only [Matrix.of_apply]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => 1)
      (by intro x hx; rw [Finset.mem_erase] at hx; rw [if_neg (Ne.symm hx.1)])]
    simp [Finset.card_erase_of_mem, Finset.card_univ]
  have h2 : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d * d := by
    rw [sq]
    simp only [adjMatrix_mul_apply]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (g := fun _ => d) (by intro x _; rw [sum_adjMatrix_row, hd x]),
      Finset.sum_const, card_neighborFinset_eq_degree, hd v, smul_eq_mul]
  omega

omit [DecidableEq V] in
/-- Multiplying the adjacency matrix of a `d`-regular graph with `d ≡ 1 [MOD p]` by the
all-ones matrix gives the all-ones matrix. -/
