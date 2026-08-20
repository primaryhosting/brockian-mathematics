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

lemma card_forest_subtype :
    Nat.card {p : Fin (N + 1) → Fin (N + 1) //
        IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => mem_forestFinset.symm)

end Graph

/-- The trees on `Fin n` form a finite type: there are only finitely many simple graphs
on a finite vertex type. -/
noncomputable instance instFintypeTreeSubtype (n : ℕ) :
    Fintype {G : SimpleGraph (Fin n) // G.IsTree} := Fintype.ofFinite _

/-- Cayley's formula: the number of labeled trees on n ≥ 1 vertices is n^(n−2)
    (counted as spanning trees of the complete graph, i.e. connected acyclic simple graphs). -/
