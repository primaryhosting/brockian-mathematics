/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem matchingOfPerm_surjective (I : Inst) (M : (biGraph I).Subgraph)
    (hM : M.IsPerfectMatching) : ∃ σ, matchingOfPerm I σ = M := by
  have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  have key : ∀ i : Fin I.size, ∃ j : Fin I.size, M.Adj (Sum.inl i) (Sum.inr j) := by
    intro i
    obtain ⟨w, hw, -⟩ := hu (Sum.inl i)
    cases w with
    | inl a => exact absurd (M.adj_sub hw) (by simp [biGraph, biAdj])
    | inr a => exact ⟨a, hw⟩
  choose f hf using key
  have huniq : ∀ (i j : Fin I.size), M.Adj (Sum.inl i) (Sum.inr j) → f i = j := by
    intro i j h
    obtain ⟨w, -, huq⟩ := hu (Sum.inl i)
    have e3 : (Sum.inr (f i) : Fin I.size ⊕ Fin I.size) = Sum.inr j :=
      (huq (Sum.inr (f i)) (hf i)).trans (huq (Sum.inr j) h).symm
    simpa using e3
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    have h2 := hf b
    rw [hab] at h1
    obtain ⟨w, -, huq⟩ := hu (Sum.inr (f b))
    have := (huq _ (M.symm h1)).trans (huq _ (M.symm h2)).symm
    simpa using this
  let σ : Equiv.Perm (Fin I.size) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ i, σ i = f i := fun i => rfl
  have hedge : ∀ i, I.edge i (σ i) := by
    intro i
    have := M.adj_sub (hf i)
    simpa [biGraph, biAdj, hσ] using this
  refine ⟨⟨σ, hedge⟩, ?_⟩
  refine SimpleGraph.Subgraph.ext (hM.2.verts_eq_univ).symm (funext₂ fun x y => propext ?_)
  constructor
  · intro h
    match x, y with
    | Sum.inl i, Sum.inr j =>
      have hfi : f i = j := h
      exact hfi ▸ hf i
    | Sum.inr j, Sum.inl i =>
      have hfi : f i = j := h
      exact M.symm (hfi ▸ hf i)
    | Sum.inl i, Sum.inl j => exact absurd h (by simp [matchingOfPerm])
    | Sum.inr i, Sum.inr j => exact absurd h (by simp [matchingOfPerm])
  · intro h
    match x, y with
    | Sum.inl i, Sum.inr j => exact huniq i j h
    | Sum.inr j, Sum.inl i => exact huniq i j (M.symm h)
    | Sum.inl i, Sum.inl j => exact absurd (M.adj_sub h) (by simp [biGraph, biAdj])
    | Sum.inr i, Sum.inr j => exact absurd (M.adj_sub h) (by simp [biGraph, biAdj])

