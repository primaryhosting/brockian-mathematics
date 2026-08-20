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

lemma iterate_eq_of_two_cycle {V : Type*} {p : V → V} {v : V} (h : p (p v) = v) (m : ℕ) :
    p^[m] v = v ∨ p^[m] v = p v := by
  have heven : ∀ k, p^[k + k] v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc p^[k + 1 + (k + 1)] v
          = p^[k + k + 2] v := by ring_nf
        _ = p^[k + k + 1 + 1] v := by ring_nf
        _ = p (p^[k + k + 1] v) := by rw [Function.iterate_succ']; rfl
        _ = p (p (p^[k + k] v)) := by rw [Function.iterate_succ']; rfl
        _ = p (p v) := by rw [ih]
        _ = v := h
  have hodd : ∀ k, p^[2 * k + 1] v = p v := by
    intro k
    rw [Function.iterate_succ']
    show p (p^[2 * k] v) = p v
    have : 2 * k = k + k := by ring
    rw [this, heven k]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; rw [hk]; exact heven k
  · right; rw [hk]; exact hodd k

/-- In a rooted forest with a single root `0`, the parent function has no `2`-cycle. -/
