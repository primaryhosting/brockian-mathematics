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

lemma exists_iterate_mem_of_cut {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → f v = g v) (hC : ∀ v ∈ C, f v = r) (hr : r ∈ S)
    (hS' : ∀ w ∈ S', w ∈ S ∨ w ∈ C) :
    ∀ (m : ℕ) (v : V), g^[m] v ∈ S' → ∃ m', f^[m'] v ∈ S := by
  -- First prove a helper: f^[k] v = g^[k] v as long as g^[i] v ∉ C for all i ≤ k
  have hagreem : ∀ k v, (∀ i ≤ k, g^[i] v ∉ C) → f^[k] v = g^[k] v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro v h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hgk : g^[k] v ∉ C := h k (Nat.le_succ k)
      rw [ih v (fun i hi => h i (Nat.le_succ_of_le hi)), hagree (g^[k] v) hgk]
  intro m v hgS'
  by_cases halt : ∀ i ≤ m, g^[i] v ∉ C
  · -- All iterates up to m are outside C, so f^[m] v = g^[m] v
    have hfmgm : f^[m] v = g^[m] v := hagreem m v halt
    by_cases hS : g^[m] v ∈ S
    · exact ⟨m, hfmgm ▸ hS⟩
    · have hCm : g^[m] v ∈ C := by simpa [hS] using hS' _ hgS'
      have hCm' : f^[m] v ∈ C := by rw [hfmgm]; exact hCm
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', show f (f^[m] v) = r from hC _ hCm']; exact hr⟩
  · -- Some iterate g^[i] v ∈ C for i ≤ m
    push_neg at halt
    -- Find the first i where g^[i] v ∈ C
    let i := Nat.find halt
    have hi_bound : i ≤ m := (Nat.find_spec halt).1
    have hi_mem : g^[i] v ∈ C := (Nat.find_spec halt).2
    -- All earlier iterates are outside C
    have hi_min : ∀ j < i, g^[j] v ∉ C := fun j hj h =>
      (Nat.find_min halt hj ⟨(Nat.le_of_lt hj).trans hi_bound, h⟩)
    -- So f^[i] v = g^[i] v (using agreem for i-1, then one more step)
    have hf_eq : f^[i] v = g^[i] v := by
      rcases i with ⟨ ⟩
      · simp
      · rename_i k
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hi_min' : ∀ j < k + 1, g^[j] v ∉ C := hi_min
        have hgik : g^[k] v ∉ C := hi_min' k (Nat.lt_succ_self k)
        rw [hagreem k v (fun j hj => hi_min' j (Nat.lt_of_le_of_lt hj (Nat.lt_succ_self k))),
            hagree (g^[k] v) hgik]
    -- Now use hf_eq and hi_mem to get f^[i+1] v = r ∈ S
    exact ⟨i + 1, by rw [Function.iterate_succ_apply', hf_eq]; rw [hC _ hi_mem]; exact hr⟩

omit [Fintype V] in
/-- Pulling reachability back when the edges into `r` are cut. -/
