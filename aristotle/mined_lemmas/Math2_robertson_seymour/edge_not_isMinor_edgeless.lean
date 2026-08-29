import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-- A finite simple graph, presented as a simple graph on the vertex set `Fin n`. -/
structure FinGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency structure. -/
  adj : SimpleGraph (Fin n)

namespace FinGraph

/-- The graph obtained from `H` by contracting the edge `{a, b}`: the vertex `b` is deleted and
its neighbourhood is added to that of `a`. -/

theorem edge_not_isMinor_edgeless (m : ℕ) :
    ¬ IsMinor ⟨2, ⊤⟩ ⟨m, ⊥⟩ := by
  intro h
  exact h.edgeless (fun u v hu => hu) 0 1 (by decide)

end FinGraph

open FinGraph

/-- **Wagner's conjecture / the graph minor theorem**, in the form asserting that the finite
graphs are well-quasi-ordered by the minor relation: every infinite sequence of finite graphs
contains an earlier member which is a minor of a later one. -/
