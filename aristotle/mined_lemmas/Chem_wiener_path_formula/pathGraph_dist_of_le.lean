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

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all
unordered pairs of distinct vertices (represented as ordered pairs `u < v`). -/

theorem pathGraph_dist_of_le {n : ℕ} (u v : Fin n) (h : (u : ℕ) ≤ (v : ℕ)) :
    (pathGraph n).dist u v = (v : ℕ) - (u : ℕ) := by
  refine le_antisymm (pathGraph_dist_le _ u v (by omega)) ?_
  by_cases hr : (pathGraph n).Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have := pathGraph_le_walk_length p
    rw [hp] at this
    rcases abs_cases (((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;> omega
  · exact absurd ((pathGraph_preconnected n) u v) hr

