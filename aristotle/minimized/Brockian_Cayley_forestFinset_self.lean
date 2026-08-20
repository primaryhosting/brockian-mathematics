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

noncomputable def forestFinset (A S : Finset V) : Finset (V → V) :=
  @Finset.filter _ (IsForest A S) (Classical.decPred _) Finset.univ

@[simp] lemma mem_forestFinset {A S : Finset V} {f : V → V} :
    f ∈ forestFinset A S ↔ IsForest A S f := by
  classical
  simp [forestFinset]

/-- If all vertices are roots, the only forest is the identity. -/

lemma forestFinset_self (A : Finset V) : forestFinset A A = {id} := by
  ext f
  simp only [mem_forestFinset, Finset.mem_singleton]
  constructor
  · intro hf
    ext v
    exact hf.fixed v (by simp)
  · rintro rfl
    exact ⟨fun v _ => rfl, fun v hv => by simp at hv, fun v hv => ⟨0, hv⟩⟩

/-- With no roots and at least one vertex there is no forest. -/
