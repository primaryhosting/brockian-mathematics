import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

namespace Math

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A matching `M` of a graph `G` gives, for every matched vertex `v`, a neighbour
`matchedVertex M v` of `v` in `G`, and this assignment is injective on the matched vertices. -/

lemma adj_matchedVertex {M : G.Subgraph} {v : V} (hv : v ∈ M.verts) (hM : M.IsMatching) :
    M.Adj v (matchedVertex M v) := by
  obtain ⟨w, hw, -⟩ := hM hv
  have h : ∃ w, M.Adj v w := ⟨w, hw⟩
  rw [matchedVertex, dif_pos h]
  exact h.choose_spec

