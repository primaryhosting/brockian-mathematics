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

lemma odd_card_goodIdx_iff {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S)
    {l : List α} (hl : (l : Multiset α) = A.val) :
    Odd (goodIdx c (A.erase z).val l).card ↔ IsRainbow c l := by
  set C := colorSeq c ∅ l with hCdef
  set D := (A.erase z).val with hDdef
  have hllen : l.length = A.card := by
    have := congrArg Multiset.card hl
    simpa using this
  have hlenEq : l.length = C.length := by rw [hCdef, colorSeq_length]
  have hlA : l.toFinset ⊆ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have hx' : x ∈ (l : Multiset α) := by exact_mod_cast hx
    rw [hl] at hx'; exact hx'
  have hCA : ∀ x ∈ C, x ∈ A := by
    intro x hx
    have := colorSeq_mem_union hc l ∅ (Finset.empty_subset _) hlA x hx
    simp only [Finset.empty_union] at this
    exact hlA this
  have hDnodup : D.Nodup := (A.erase z).nodup
  have hzD : z ∉ D := by
    simp only [hDdef, Finset.mem_val]
    exact Finset.notMem_erase z A
  have key : ∀ i (hi : i < C.length),
      (((C.eraseIdx i : List α) : Multiset α) = D ↔ (C : Multiset α) = C[i] ::ₘ D) := by
    intro i hi
    rw [coe_eraseIdx C i hi]
    constructor
    · intro h
      rw [← h]
      exact (Multiset.cons_erase (by exact_mod_cast List.getElem_mem hi)).symm
    · intro h
      rw [h, Multiset.erase_cons_head]
  by_cases hex : ∃ v, (C : Multiset α) = v ::ₘ D
  · obtain ⟨v, hv⟩ := hex
    have hvC : v ∈ C := by
      have : v ∈ (C : Multiset α) := by rw [hv]; exact Multiset.mem_cons_self _ _
      exact_mod_cast this
    have hfilter : goodIdx c D l = (Finset.range C.length).filter (fun i => C[i]? = some v) := by
      rw [goodIdx, ← hCdef, hlenEq]
      refine Finset.filter_congr ?_
      intro i hi
      rw [Finset.mem_range] at hi
      rw [key i hi, hv, List.getElem?_eq_getElem hi]
      simp only [Option.some_inj]
      constructor
      · intro h; exact ((Multiset.cons_inj_left D).mp h).symm
      · intro h; rw [h]
    have hcard : (goodIdx c D l).card = Multiset.count v (C : Multiset α) := by
      rw [hfilter, card_filter_getElem?_eq, Multiset.coe_count]
    rw [hv, Multiset.count_cons_self] at hcard
    by_cases hvz : v = z
    · subst hvz
      have hcount : Multiset.count v D = 0 := Multiset.count_eq_zero.mpr hzD
      rw [hcount] at hcard
      have hCA' : (C : Multiset α) = A.val := by
        rw [hv, hDdef]; exact Multiset.cons_erase hz
      have : IsRainbow c l := by
        show C.Nodup
        rw [← Multiset.coe_nodup, hCA']
        exact A.nodup
      simp [hcard, this]
    · have hvA : v ∈ A := hCA v hvC
      have hvD : v ∈ D := by
        rw [hDdef]
        exact Multiset.mem_erase_of_ne hvz |>.mpr (by exact_mod_cast hvA)
      have hcount : Multiset.count v D = 1 := Multiset.count_eq_one_of_mem hDnodup hvD
      rw [hcount] at hcard
      have hnr : ¬ IsRainbow c l := by
        show ¬ C.Nodup
        rw [← Multiset.coe_nodup, hv]
        intro hnd
        have := Multiset.nodup_iff_count_le_one.mp hnd v
        rw [Multiset.count_cons_self, hcount] at this
        omega
      simp only [hcard, hnr, iff_false]
      decide
  · have hempty : goodIdx c D l = ∅ := by
      rw [goodIdx, ← hCdef, hlenEq]
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro i hi
      rw [Finset.mem_range] at hi
      rw [key i hi]
      exact fun h => hex ⟨C[i], h⟩
    have hnr : ¬ IsRainbow c l := by
      intro hnd
      apply hex
      refine ⟨z, ?_⟩
      have hCnd : (C : Multiset α).Nodup := Multiset.coe_nodup.mpr hnd
      have hsub : C.toFinset ⊆ A := fun x hx => hCA x (List.mem_toFinset.mp hx)
      have hcardC : C.toFinset.card = A.card := by
        rw [List.toFinset_card_of_nodup hnd, ← hlenEq, hllen]
      have : C.toFinset = A := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardC.symm)
      have hCval : (C : Multiset α) = A.val := by
        rw [← this, List.toFinset_val, List.Nodup.dedup (hnd : C.Nodup)]
      rw [hCval, hDdef]
      exact (Multiset.cons_erase hz).symm
    simp [hempty, hnr]

/-! ### Cells, colours and the top face -/

