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

lemma graphOf_injOn_aux {p q : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p)
    (hq : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} q)
    (h : graphOf p = graphOf q) :
    ∀ (m : ℕ) (v : Fin (N + 1)), p^[m] v = 0 → p v = q v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv
  by_cases h0 : v = 0
  · subst h0
    rw [hp.fixed 0 (by simp), hq.fixed 0 (by simp)]
  · have hadj : (graphOf q).Adj v (p v) := h ▸ graphOf_adj_parent hp h0
    obtain ⟨hne, hcase⟩ := graphOf_adj.mp hadj
    rcases hcase with ⟨-, h1⟩ | ⟨hpv0, h2⟩
    · exact h1.symm
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := by
        cases m with
        | zero => exact absurd hv h0
        | succ j => exact ⟨j, rfl⟩
      have hj : p^[j] (p v) = 0 := by rw [← Function.iterate_succ_apply]; exact hv
      have hpp : p (p v) = v := by rw [ih j (by omega) (p v) hj, h2]
      exact absurd hpp (fun hc => (not_two_cycle hp h0 hc).elim)

