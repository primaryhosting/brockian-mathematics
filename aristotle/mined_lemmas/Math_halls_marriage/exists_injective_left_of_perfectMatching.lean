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

theorem exists_injective_left_of_perfectMatching {G : SimpleGraph (α ⊕ β)}
    (hbip : IsBipartiteSum G) {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, G.Adj (Sum.inl a) (Sum.inr (f a)) := by
  choose f hf using exists_right_of_perfectMatching hbip hM
  refine ⟨f, ?_, fun a => M.adj_sub (hf a)⟩
  intro a₁ a₂ h
  have := hM.1.eq_of_adj_right (hf a₁) (h ▸ hf a₂)
  simpa using this

/-- A perfect matching of a bipartite graph yields an injection from the right side into the
left side along edges of the graph. -/
