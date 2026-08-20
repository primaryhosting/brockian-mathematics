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

theorem adjMatrix_sq_apply_of_ne (hG : IsFriendship G) {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  obtain ⟨u, ⟨h1, h2⟩, huniq⟩ := hG v w hvw
  rw [sq, Matrix.mul_apply, Finset.sum_eq_single u]
  · simp [adjMatrix_apply, h1, h2.symm]
  · intro b _ hb
    rcases Classical.em (G.Adj v b) with hvb | hvb
    · have hbw : ¬ G.Adj b w := fun hbw => hb (huniq b ⟨hvb, hbw.symm⟩)
      simp [adjMatrix_apply, hbw]
    · simp [adjMatrix_apply, hvb]
  · intro h; exact absurd (Finset.mem_univ u) h

/-- For nonadjacent `v w`, the `(v, w)` entry of the cube of the adjacency matrix is the
degree of `v`: length-3 walks from `v` to `w` correspond to neighbours of `v`. -/
