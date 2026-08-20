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

lemma isForest_uncut {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S)
    {g : V → V} (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : IsForest A S (uncut C r g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hvC : v ∉ C := fun h => hv (hCA h)
    simp [uncut, hvC]
    by_cases hvA : v ∈ A
    · by_cases hvS : v ∈ S
      · have hvnearerase : v ∉ A.erase r \ (S.erase r ∪ C) := by
          simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
          tauto
        exact hg.fixed v hvnearerase
      · exfalso; simp_all
    · have hvnearerase : v ∉ A.erase r := fun h => hvA (Finset.mem_of_mem_erase h)
      exact hg.fixed v (by simp_all)
  · intro v hv
    simp at hv
    by_cases hvC : v ∈ C
    · simp [uncut, hvC]; exact hSA hr
    · simp [uncut, hvC]
      have hvne : v ≠ r := fun h => hv.2 (h.symm ▸ hr)
      have hvAerase : v ∈ A.erase r := by simp [hv.1, hvne]
      have hvnotin : v ∉ S.erase r ∪ C := by simp_all [Finset.mem_union]
      exact Finset.mem_of_mem_erase (hg.maps v (Finset.mem_sdiff.mpr ⟨hvAerase, hvnotin⟩))
  · intro v hv
    by_cases hvS : v ∈ S
    · exact ⟨0, hvS⟩
    · -- v ∉ S, so we use exists_iterate_mem_of_cut
      have hvAerase : v ∈ A.erase r := by simp [hv]; intro hvr; exact hvS (hvr ▸ hr)
      obtain ⟨k, hk⟩ := hg.reaches v hvAerase
      -- the `uncut` function agrees with `g` off `C`, and sends `C` to the root `r`
      refine exists_iterate_mem_of_cut (f := uncut C r g) (g := g) (C := C) (S := S)
        (S' := S.erase r ∪ C) (r := r) (fun x hx => by simp [uncut, hx])
        (fun x hx => by simp [uncut, hx]) hr (fun w hw => ?_) k v hk
      rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl (Finset.mem_of_mem_erase hw)
      · exact Or.inr hw

omit [Fintype V] in
