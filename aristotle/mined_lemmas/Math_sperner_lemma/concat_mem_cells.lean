import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of this commit) contains *Sperner's theorem* on antichains
(`IsAntichain.sperner`) but **no** Sperner *lemma* about triangulated simplices;
`exact?`/`apply?`/`rw?` therefore have nothing to close this with, and the whole
development below is built from scratch.

## Formalisation

We work with the **barycentric subdivision** of a simplex.  Let `A : Finset α` be the
vertex set of a simplex `Δ(A)` (so `Δ(A)` has dimension `A.card - 1`).  The vertices of
the barycentric subdivision of `Δ(A)` are the barycentres of the faces of `Δ(A)`, i.e.
the nonempty subsets `S ⊆ A`, and the top-dimensional cells are the maximal flags
`S₁ ⊊ S₂ ⊊ ⋯ ⊊ S_k = A` (with `|S_i| = i`).  Such a flag is the same thing as an
ordering `a₁, a₂, …, a_k` of `A` (take `S_i = {a₁, …, a_i}`), so we encode a cell as a
list `l` whose underlying multiset is `A.val` (see `Math.cells`).

A **Sperner colouring** assigns to each vertex `S` of the subdivision a colour
`c S ∈ S` (the barycentre of a face must get a colour of one of the vertices of that
face).  A cell is **rainbow** (or "completely labelled") when its `k` vertices carry
`k` pairwise distinct colours.  `Math.colorSeq c ∅ l` is the list of colours of the
vertices of the cell `l`, listed along the flag.

The main result, `Math.sperner_lemma`, states that the number of rainbow cells is odd.
The section "The flag of faces of a cell" at the end records the dictionary between a
cell `l` and the corresponding maximal flag `Math.flagOf l 0 ⊊ ⋯ ⊊ Math.flagOf l (k-1) = A`
of faces of `Δ(A)`, and checks that the colours of the cell are exactly the colours of
the barycentres of that flag.
-/

open Finset List

namespace Math

variable {α : Type*} [DecidableEq α]

/-! ### The colours along a flag -/

/-- `colorSeq c acc l` is the list of colours `c (acc ∪ {a₁,…,a_i})`, `i = 1 … |l|`,
of the vertices of the flag determined by the ordering `l = [a₁, …, a_n]`
(started from the face `acc`). -/

lemma concat_mem_cells {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) {m : List α}
    (hm : m ∈ rainbowCells c (A.erase z)) :
    (m ++ [z]) ∈ cells A ∧
      ((colorSeq c ∅ (m ++ [z]).dropLast : List α) : Multiset α) = (A.erase z).val := by
  rw [rainbowCells, Finset.mem_filter] at hm
  obtain ⟨hm1, hm2⟩ := hm
  have hval : ((m ++ [z] : List α) : Multiset α) = A.val := by
    have h : ((m ++ [z] : List α) : Multiset α) = z ::ₘ (m : Multiset α) :=
      Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)
    rw [h, mem_cells.mp hm1]
    exact Multiset.cons_erase hz
  refine ⟨mem_cells.mpr hval, ?_⟩
  rw [List.dropLast_concat]
  exact coe_colorSeq_of_rainbow
    (fun S hS hSA => hc S hS (hSA.trans (Finset.erase_subset _ _))) hm1 hm2

/-! ### The main theorem -/

/-- **Sperner's lemma.**  Let `Δ(A)` be the simplex with vertex set `A`, barycentrically
subdivided; its cells are the maximal flags of faces of `Δ(A)`, encoded as orderings of
`A`.  For any Sperner colouring `c` (each barycentre `S` receives a colour `c S ∈ S`),
the number of rainbow cells is odd. -/
