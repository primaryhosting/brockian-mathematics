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

theorem exists_isRegular_of_not_hasPolitician [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hG : IsFriendship G) (hp : ¬ HasPolitician G) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  classical
  have v₀ := Classical.arbitrary V
  refine ⟨G.degree v₀, fun x => ?_⟩
  by_cases hvx : G.Adj v₀ x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  -- both `v₀` and `x` have non-neighbours
  simp only [HasPolitician, not_exists, not_forall] at hp
  obtain ⟨w, hvw', hvw⟩ : ∃ w, v₀ ≠ w ∧ ¬ G.Adj v₀ w := by
    obtain ⟨w, hw⟩ := hp v₀
    exact ⟨w, hw.1, hw.2⟩
  obtain ⟨y, hxy', hxy⟩ : ∃ y, x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨y, hy⟩ := hp x
    exact ⟨y, hy.1, hy.2⟩
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v₀ y
  swap
  · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine (degree_eq_of_not_adj hG (v := w) (w := y) ?_).symm
  intro hwy
  obtain ⟨u, _, huniq⟩ := hG v₀ w hvw'
  exact hxy' ((huniq x ⟨hvx, hxw.symm⟩).trans (huniq y ⟨hvy, hwy⟩).symm)

section Regular

variable [DecidableEq V] [DecidableRel G.Adj]

/-- The square of the adjacency matrix of a `d`-regular friendship graph. -/
