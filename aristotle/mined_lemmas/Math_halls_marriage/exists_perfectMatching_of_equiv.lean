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

theorem exists_perfectMatching_of_equiv {G : SimpleGraph (α ⊕ β)} (e : α ≃ β)
    (he : ∀ a, G.Adj (Sum.inl a) (Sum.inr (e a))) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  refine ⟨{ verts := Set.univ
            Adj := fun x y =>
              (∃ a, x = Sum.inl a ∧ y = Sum.inr (e a)) ∨ (∃ a, y = Sum.inl a ∧ x = Sum.inr (e a))
            adj_sub := ?_
            edge_vert := ?_
            symm := ?_ }, ?_, ?_⟩
  · rintro x y (⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact he a
    · exact (he a).symm
  · intro _ _ _; trivial
  · rintro x y (⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact Or.inr ⟨a, rfl, rfl⟩
    · exact Or.inl ⟨a, rfl, rfl⟩
  · rintro v -
    cases v with
    | inl a =>
        refine ⟨Sum.inr (e a), Or.inl ⟨a, rfl, rfl⟩, ?_⟩
        rintro y (⟨a', ha', rfl⟩ | ⟨a', rfl, ha'⟩)
        · simp only [Sum.inl.injEq] at ha'; subst ha'; rfl
        · exact absurd ha' (by simp)
    | inr b =>
        refine ⟨Sum.inl (e.symm b), Or.inr ⟨e.symm b, rfl, by simp⟩, ?_⟩
        rintro y (⟨a', ha', rfl⟩ | ⟨a', rfl, ha'⟩)
        · exact absurd ha' (by simp)
        · simp only [Sum.inr.injEq] at ha'
          subst ha'
          simp
  · intro v; trivial

/-- Two injections in opposite directions along the edges of a bipartite graph give a perfect
matching. -/
