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

theorem exists_perfectMatching_of_injective [Fintype α] [Fintype β] {G : SimpleGraph (α ⊕ β)}
    (hf : ∃ f : α → β, Function.Injective f ∧ ∀ a, G.Adj (Sum.inl a) (Sum.inr (f a)))
    (hg : ∃ g : β → α, Function.Injective g ∧ ∀ b, G.Adj (Sum.inl (g b)) (Sum.inr b)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨f, hfinj, hfadj⟩ := hf
  obtain ⟨g, hginj, -⟩ := hg
  have hcard : Fintype.card α = Fintype.card β :=
    le_antisymm (Fintype.card_le_of_injective f hfinj) (Fintype.card_le_of_injective g hginj)
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩
  refine exists_perfectMatching_of_equiv (Equiv.ofBijective f hbij) ?_
  intro a
  simpa [Equiv.ofBijective] using hfadj a

/-- **Hall's Marriage Theorem** for bipartite graphs.

Let `G` be a bipartite graph on the (finite) vertex type `α ⊕ β`, meaning that every edge joins
a vertex on the left to a vertex on the right.  Then `G` has a perfect matching if and only if
Hall's condition holds on both sides: every set `s` of left vertices has at least `#s`
neighbours, and every set `t` of right vertices has at least `#t` neighbours. -/
