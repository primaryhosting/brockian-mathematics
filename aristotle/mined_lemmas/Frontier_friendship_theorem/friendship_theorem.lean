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

theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  classical
  by_contra hp
  obtain ⟨d, hd⟩ := exists_isRegular_of_not_hasPolitician (G := G) hG hp
  rcases lt_or_ge d 3 with hlt | hge
  · exact hp (hasPolitician_of_degree_le_two (d := d) hG hd (by omega))
  · exact false_of_three_le_degree hG hd hge

/-- The friendship theorem, phrased with `Fintype.card (G.commonNeighbors v w) = 1`. -/
