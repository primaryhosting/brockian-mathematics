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

lemma dropLast_mem_rainbowCells {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) {l : List α} (hl : l ∈ cells A)
    (hd : ((colorSeq c ∅ l.dropLast : List α) : Multiset α) = (A.erase z).val) :
    l.dropLast ∈ rainbowCells c (A.erase z) ∧ l = l.dropLast ++ [z] := by
  have hlen : l.length = A.card := length_of_mem_cells hl
  have hlne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    exact absurd (Finset.card_pos.mpr ⟨z, hz⟩) (by omega)
  have hmnd : l.dropLast.Nodup := (List.dropLast_sublist l).nodup (nodup_of_mem_cells hl)
  have hmlen : l.dropLast.length = (A.erase z).card := by
    rw [List.length_dropLast, hlen, Finset.card_erase_of_mem hz]
  have hmA : l.dropLast.toFinset ⊆ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have : x ∈ l := (List.dropLast_sublist l).mem hx
    rw [← toFinset_of_mem_cells hl, List.mem_toFinset]
    exact this
  have hsub : A.erase z ⊆ l.dropLast.toFinset := by
    intro x hx
    have hx1 : x ∈ ((colorSeq c ∅ l.dropLast : List α) : Multiset α) := by
      rw [hd]; exact hx
    have hx2 : x ∈ colorSeq c ∅ l.dropLast := by exact_mod_cast hx1
    exact colorSeq_mem_of_mem_cells hc hmA hx2
  have hmval : (l.dropLast : Multiset α) = (A.erase z).val :=
    coe_eq_val_of_nodup hmnd hmlen (Or.inr hsub)
  refine ⟨?_, ?_⟩
  · rw [rainbowCells, Finset.mem_filter]
    refine ⟨mem_cells.mpr hmval, ?_⟩
    show (colorSeq c ∅ l.dropLast).Nodup
    rw [← Multiset.coe_nodup, hd]
    exact (A.erase z).nodup
  · have hlast := List.dropLast_append_getLast hlne
    set x := l.getLast hlne with hxdef
    have h1 : (l : Multiset α) = x ::ₘ (l.dropLast : Multiset α) := by
      conv_lhs => rw [← hlast]
      exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)
    have h2 : x ::ₘ (A.erase z).val = z ::ₘ (A.erase z).val := by
      have hA : (l : Multiset α) = A.val := mem_cells.mp hl
      rw [h1, hmval] at hA
      rw [hA]
      exact (Multiset.cons_erase hz).symm
    have hxz : x = z := (Multiset.cons_inj_left _).mp h2
    conv_lhs => rw [← hlast]
    rw [hxz]

/-- Conversely, appending the top face to a rainbow cell of the facet `Δ(A \ {z})`
produces a cell of `Δ(A)` whose last door has colours `A \ {z}`. -/
