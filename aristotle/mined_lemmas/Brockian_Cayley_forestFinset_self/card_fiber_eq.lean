import Mathlib

namespace Brockian.Cayley

open Finset

/-!
# Cayley's formula

The number of labeled trees on `n` vertices is `n ^ (n - 2)`.

The proof goes through *rooted forests*, encoded as "parent functions": a rooted forest on a
vertex set `A` with set of roots `S ⊆ A` is a function `f : V → V` which fixes everything
outside `A \ S`, maps `A \ S` into `A`, and such that iterating `f` from any vertex of `A`
eventually lands in `S`.

The main counting statement is
`|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`,
proved by induction on `|A|` (deleting a root and summing over the set of its children).

Specialising to `A = univ` and `S = {0}` in `Fin n` and putting rooted forests with a single
root in bijection with trees gives Cayley's formula.
-/

/-! ### Rooted forests, encoded by parent functions -/

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsForest A S f` says that `f` is the parent function of a rooted forest on the vertex
set `A` whose set of roots is `S`. -/
structure IsForest (A S : Finset V) (f : V → V) : Prop where
  /-- Vertices which are not non-root vertices of the forest are fixed. -/
  fixed : ∀ v, v ∉ A \ S → f v = v
  /-- The parent of a non-root vertex is a vertex. -/
  maps : ∀ v ∈ A \ S, f v ∈ A
  /-- Iterating the parent function eventually reaches a root. -/
  reaches : ∀ v ∈ A, ∃ m, f^[m] v ∈ S

/-- The finset of rooted forests on `A` with roots `S`, encoded by parent functions. -/

lemma card_fiber_eq {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S) :
    ((forestFinset A S).filter (fun f => children A S r f = C)).card
      = (forestFinset (A.erase r) (S.erase r ∪ C)).card := by
  refine Finset.card_nbij' (cut C) (uncut C r) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := isForest_cut hr hf.1
    rw [hf.2] at h
    simpa using h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset]
    exact ⟨isForest_uncut hr hSA hCA hg, children_uncut hr hCA hg⟩
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := uncut_cut A S r f
    rw [hf.2] at h
    exact h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    exact cut_uncut hg

/-- Deleting a root `r` splits the forests on `A` with roots `S` according to the set `C` of
children of `r`. -/
