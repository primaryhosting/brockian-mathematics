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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {α β : Type*}

/-- A simple graph on `α ⊕ β` is *bipartite* (with respect to the given splitting of its
vertex type) if every edge joins a vertex of `α` to a vertex of `β`. -/

theorem exists_left_of_perfectMatching {G : SimpleGraph (α ⊕ β)} (hbip : IsBipartiteSum G)
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (b : β) :
    ∃ a : α, M.Adj (Sum.inl a) (Sum.inr b) := by
  obtain ⟨w, hw, -⟩ := hM.1 (hM.2 (Sum.inr b))
  cases w with
  | inl a => exact ⟨a, hw.symm⟩
  | inr b' =>
      exact absurd (hbip _ _ (M.adj_sub hw)) (by simp)

/-- A perfect matching of a bipartite graph yields an injection from the left side into the
right side along edges of the graph. -/
