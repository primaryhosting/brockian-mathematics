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

lemma colorSeq_mem_union {c : Finset α → α} {B : Finset α}
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ B → c S ∈ S) :
    ∀ (l : List α) (acc : Finset α), acc ⊆ B → l.toFinset ⊆ B →
      ∀ x ∈ colorSeq c acc l, x ∈ acc ∪ l.toFinset := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro acc hacc hl x hx
    simp only [colorSeq_cons, List.mem_cons] at hx
    have haB : a ∈ B := hl (by simp)
    have htB : t.toFinset ⊆ B := fun y hy => hl (by simp only [List.toFinset_cons]; exact Finset.mem_insert_of_mem hy)
    have hins : insert a acc ⊆ B := Finset.insert_subset haB hacc
    rcases hx with rfl | hx
    · have := hc (insert a acc) ⟨a, Finset.mem_insert_self _ _⟩ hins
      simp only [Finset.mem_insert] at this
      rcases this with h | h
      · simp [h]
      · simp [h]
    · have := ih (insert a acc) hins htB x hx
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at this ⊢
      tauto

