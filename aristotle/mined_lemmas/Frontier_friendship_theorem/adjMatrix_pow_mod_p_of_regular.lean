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

theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (hG : IsFriendship G)
    (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    (G.adjMatrix (ZMod p) ^ k) = Matrix.of fun _ _ => 1 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [adjMatrix_sq_of_regular hG hd]
    ext v w
    by_cases h : v = w <;> simp [h, dmod]
  | succ k _ ih =>
    rw [pow_succ', ih, adjMatrix_mul_ones dmod hd]

/-- A `d`-regular friendship graph with `3 ≤ d` cannot exist. -/
