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

theorem friendship_theorem' {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : ∀ v w : V, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  refine friendship_theorem (fun v w hvw => ?_)
  obtain ⟨⟨u, hu⟩, huniq⟩ := Fintype.card_eq_one_iff.mp (hG v w hvw)
  rw [mem_commonNeighbors] at hu
  exact ⟨u, hu, fun y hy => congrArg Subtype.val (huniq ⟨y, (mem_commonNeighbors G).mpr hy⟩)⟩

/-- The hypothesis of the friendship theorem is satisfiable: the triangle is a friendship
graph (so the theorem is not vacuous). -/
example : ∀ v w : Fin 3, v ≠ w →
    ∃! u : Fin 3, (completeGraph (Fin 3)).Adj v u ∧ (completeGraph (Fin 3)).Adj w u := by
  simp only [ExistsUnique, completeGraph, top_adj]
  decide

end Frontier

