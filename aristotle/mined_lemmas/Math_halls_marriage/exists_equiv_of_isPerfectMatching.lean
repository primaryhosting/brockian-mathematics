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

set_option grind.warning false

namespace Math

open Finset Function

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` determined by a relation `r : V → W → Prop`:
the only edges join a vertex `v` of the left part to a vertex `w` of the right part,
and such an edge is present exactly when `r v w` holds. -/

lemma exists_equiv_of_isPerfectMatching {r : V → W → Prop} {M : (bipartiteGraph r).Subgraph}
    (hM : M.IsPerfectMatching) : ∃ e : V ≃ W, ∀ v, r v (e v) := by
  have key : ∀ v : V, ∃! w : W, M.Adj (Sum.inl v) (Sum.inr w) := by
    intro v
    obtain ⟨x, hx, hu⟩ := hM.1 (hM.2 (Sum.inl v))
    cases x with
    | inl v' => exact absurd (M.adj_sub hx) (by simp)
    | inr w =>
      refine ⟨w, hx, ?_⟩
      intro w' hw'
      have := hu (Sum.inr w') hw'
      simpa using this
  have key2 : ∀ w : W, ∃! v : V, M.Adj (Sum.inr w) (Sum.inl v) := by
    intro w
    obtain ⟨x, hx, hu⟩ := hM.1 (hM.2 (Sum.inr w))
    cases x with
    | inr w' => exact absurd (M.adj_sub hx) (by simp)
    | inl v =>
      refine ⟨v, hx, ?_⟩
      intro v' hv'
      have := hu (Sum.inl v') hv'
      simpa using this
  classical
  refine ⟨⟨fun v => (key v).choose, fun w => (key2 w).choose, ?_, ?_⟩, ?_⟩
  · intro v
    have h1 : M.Adj (Sum.inl v) (Sum.inr ((key v).choose)) := (key v).choose_spec.1
    exact ((key2 ((key v).choose)).choose_spec.2 v h1.symm).symm
  · intro w
    have h1 : M.Adj (Sum.inr w) (Sum.inl ((key2 w).choose)) := (key2 w).choose_spec.1
    exact ((key ((key2 w).choose)).choose_spec.2 w h1.symm).symm
  · intro v
    have h1 : M.Adj (Sum.inl v) (Sum.inr ((key v).choose)) := (key v).choose_spec.1
    simpa using M.adj_sub h1

/-- The bipartite graph of `r` has a perfect matching iff there is an equivalence between the
two sides compatible with `r`. -/
