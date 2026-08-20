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

lemma isForest_cut {A S : Finset V} {r : V} (hr : r ∈ S) {f : V → V}
    (hf : IsForest A S f) :
    IsForest (A.erase r) (S.erase r ∪ children A S r f) (cut (children A S r f) f) := by
  set C := children A S r f with hCdef
  have hmemC : ∀ v, v ∈ C ↔ (v ∈ A ∧ v ∉ S ∧ f v = r) := by
    intro v
    simp [hCdef, children, Finset.mem_filter, Finset.mem_sdiff, and_assoc]
  have hset : ∀ v, v ∈ (A.erase r) \ (S.erase r ∪ C) ↔ (v ∈ A ∧ v ∉ S ∧ v ∉ C) := by
    intro v
    constructor
    · intro h
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or] at h
      exact ⟨h.1.2, fun hvS => h.2.1 ⟨h.1.1, hvS⟩, h.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      have hvr : v ≠ r := fun hh => h2 (hh ▸ hr)
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or]
      exact ⟨⟨hvr, h1⟩, fun hcon => h2 hcon.2, h3⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · by_cases hvC : v ∈ C
    · simp [cut, hvC]
    · have : v ∉ A \ S := by
        intro hcon
        exact hv ((hset v).2 ⟨(Finset.mem_sdiff.mp hcon).1, (Finset.mem_sdiff.mp hcon).2, hvC⟩)
      simp [cut, hvC, hf.fixed v this]
  · obtain ⟨hvA, hvS, hvC⟩ := (hset v).1 hv
    have hfv : f v ∈ A := hf.maps v (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩)
    have hne : f v ≠ r := fun hcon => hvC ((hmemC v).2 ⟨hvA, hvS, hcon⟩)
    simp only [cut, if_neg hvC]
    exact Finset.mem_erase.2 ⟨hne, hfv⟩
  · have hvA : v ∈ A := Finset.mem_of_mem_erase hv
    have hvr : v ≠ r := (Finset.mem_erase.mp hv).1
    obtain ⟨m, hm⟩ := hf.reaches v hvA
    refine exists_iterate_mem_of_cut' (f := f) (g := cut C f) (C := C) (S := S)
      (S' := S.erase r ∪ C) (r := r) ?_ ?_ ?_ ?_ m v hvr hm
    · intro w hw
      simp [cut, hw]
    · exact Finset.subset_union_right
    · intro w hwS hwr
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwr, hwS⟩)
    · intro w hwr hwS hwC hcon
      by_cases hwA : w ∈ A
      · exact hwC ((hmemC w).2 ⟨hwA, hwS, hcon⟩)
      · rw [hf.fixed w (fun hcon2 => hwA (Finset.mem_sdiff.mp hcon2).1)] at hcon
        exact hwr hcon

omit [Fintype V] in
