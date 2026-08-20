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

theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hcard : Fintype.card {G : SimpleGraph (Fin (N + 1)) // G.IsTree}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
    rw [← Nat.card_eq_fintype_card, card_tree_eq_card_forest, card_forest_subtype]
  have h := card_forestFinset (Finset.univ : Finset (Fin (N + 1))) {0} (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton, one_mul,
    Nat.add_sub_cancel] at h
  rw [hcard]
  refine Nat.eq_of_mul_eq_mul_left (show 0 < N + 1 by omega) ?_
  rw [h]
  rcases N with _ | N
  · simp
  · rw [show N + 1 + 1 - 2 = N by omega]
    ring

end Brockian.Cayley

