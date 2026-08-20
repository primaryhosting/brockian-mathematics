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

theorem exists_injective_right_of_perfectMatching {G : SimpleGraph (α ⊕ β)}
    (hbip : IsBipartiteSum G) {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ g : β → α, Function.Injective g ∧ ∀ b, G.Adj (Sum.inl (g b)) (Sum.inr b) := by
  choose g hg using exists_left_of_perfectMatching hbip hM
  refine ⟨g, ?_, fun b => M.adj_sub (hg b)⟩
  intro b₁ b₂ h
  have h2 : M.Adj (Sum.inl (g b₁)) (Sum.inr b₂) := by rw [h]; exact hg b₂
  have := hM.1.eq_of_adj_left (hg b₁) h2
  simpa using this

/-- An equivalence `α ≃ β` all of whose graphs are edges gives a perfect matching. -/
