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

private lemma sperner_aux : ∀ (n : ℕ) (A : Finset α) (c : Finset α → α), A.card = n →
    (∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) → Odd (rainbowCells c A).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A c hcard hc
    rcases Finset.eq_empty_or_nonempty A with rfl | hA
    · have h1 : rainbowCells c (∅ : Finset α) = {[]} := by
        rw [rainbowCells, cells_empty, Finset.filter_eq_self.mpr]
        intro l hl
        rw [Finset.mem_singleton] at hl
        subst hl
        exact List.nodup_nil
      rw [h1]
      simp
    · obtain ⟨z, hz⟩ := hA
      have hk : 1 ≤ A.card := Finset.card_pos.mpr ⟨z, hz⟩
      set k := A.card with hkdef
      set D := (A.erase z).val with hDdef
      set S := ((cells A) ×ˢ Finset.range k).filter
        (fun p => (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D) with hSdef
      -- Facts about membership in `S`.
      have hmemS : ∀ p : List α × ℕ, p ∈ S →
          p.1 ∈ cells A ∧ p.2 < k ∧
            (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D := by
        intro p hp
        rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        exact ⟨hp.1.1, hp.1.2, hp.2⟩
      -- Step 1: counting the doors cell by cell.
      have hScard : S.card = ∑ l ∈ cells A, (goodIdx c D l).card := by
        rw [hSdef, Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [goodIdx, Finset.card_filter, length_of_mem_cells hl]
      have hstep1 : ((S.card : ℕ) : ZMod 2) = ((rainbowCells c A).card : ZMod 2) := by
        rw [hScard, rainbowCells, Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun l hl => ?_
        by_cases hr : IsRainbow c l
        · have hodd : Odd (goodIdx c D l).card :=
            (odd_card_goodIdx_iff hz hc (mem_cells.mp hl)).mpr hr
          rw [ZMod.natCast_eq_one_iff_odd.mpr hodd]
          simp [hr]
        · have hev : Even (goodIdx c D l).card := by
            rw [← Nat.not_odd_iff_even]
            exact fun h => hr ((odd_card_goodIdx_iff hz hc (mem_cells.mp hl)).mp h)
          rw [ZMod.natCast_eq_zero_iff_even.mpr hev]
          simp [hr]
      -- Step 2: the interior doors cancel in pairs.
      have hmid : (((S.filter (fun p => ¬ p.2 = k - 1)).card : ℕ) : ZMod 2) = 0 := by
        have hfacts : ∀ p : List α × ℕ, p ∈ S.filter (fun p => ¬ p.2 = k - 1) →
            p.1 ∈ cells A ∧ p.2 + 1 < p.1.length ∧
              (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D ∧ ¬ p.2 = k - 1 := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨h1, h2, h3⟩ := hmemS p hp.1
          refine ⟨h1, ?_, h3, hp.2⟩
          rw [length_of_mem_cells h1]
          omega
        have h0 : ∑ _p ∈ S.filter (fun p => ¬ p.2 = k - 1), (1 : ZMod 2) = 0 := by
          refine Finset.sum_involution (fun p _ => (swapAt p.1 p.2, p.2)) (fun a ha => by decide)
            ?_ ?_ ?_
          · intro a ha _
            obtain ⟨h1, h2, _, _⟩ := hfacts a ha
            intro hcon
            exact swapAt_ne a.1 a.2 (nodup_of_mem_cells h1) h2 (congrArg Prod.fst hcon)
          · intro a ha
            obtain ⟨h1, h2, h3, h4⟩ := hfacts a ha
            show (swapAt a.1 a.2, a.2) ∈ S.filter (fun p => ¬ p.2 = k - 1)
            refine Finset.mem_filter.mpr ⟨?_, h4⟩
            rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · exact mem_cells.mpr
                ((Multiset.coe_eq_coe.mpr (swapAt_perm a.1 a.2)).trans (mem_cells.mp h1))
            · show a.2 < k
              have hlen : a.1.length = k := (length_of_mem_cells h1).trans hkdef.symm
              omega
            · show (((colorSeq c ∅ (swapAt a.1 a.2)).eraseIdx a.2 : List α) : Multiset α) = D
              rw [colorSeq_swapAt_eraseIdx c a.1 a.2 ∅ h2]; exact h3
          · intro a ha
            obtain ⟨h1, h2, _, _⟩ := hfacts a ha
            show (swapAt (swapAt a.1 a.2) a.2, a.2) = a
            rw [swapAt_swapAt a.1 a.2 h2]
        simpa using h0
      -- Step 3: the boundary doors are the rainbow cells of the facet.
      have htop : (S.filter (fun p => p.2 = k - 1)).card = (rainbowCells c (A.erase z)).card := by
        have hkey : ∀ p : List α × ℕ, p ∈ S.filter (fun p => p.2 = k - 1) →
            p.1.dropLast ∈ rainbowCells c (A.erase z) ∧ p.1 = p.1.dropLast ++ [z] := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨h1, _, h3⟩ := hmemS p hp.1
          have hlen : (colorSeq c ∅ p.1).length = k := by
            rw [colorSeq_length, length_of_mem_cells h1]
          rw [hp.2, ← hlen, List.eraseIdx_length_sub_one, ← colorSeq_dropLast] at h3
          exact dropLast_mem_rainbowCells hz hc h1 h3
        refine Finset.card_bij (fun p _ => p.1.dropLast) (fun p hp => (hkey p hp).1) ?_ ?_
        · intro p hp q hq hpq
          rw [Finset.mem_filter] at hp hq
          have h1 := (hkey p (Finset.mem_filter.mpr hp)).2
          have h2 := (hkey q (Finset.mem_filter.mpr hq)).2
          have hpq' : p.1.dropLast = q.1.dropLast := hpq
          have hfst : p.1 = q.1 := by rw [h1, h2, hpq']
          exact Prod.ext hfst (by rw [hp.2, hq.2])
        · intro m hm
          obtain ⟨h1, h2⟩ := concat_mem_cells hz hc hm
          refine ⟨(m ++ [z], k - 1), ?_, by show (m ++ [z]).dropLast = m; simp⟩
          rw [Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          have hlen : (colorSeq c ∅ (m ++ [z])).length = k := by
            rw [colorSeq_length, length_of_mem_cells h1]
          refine ⟨⟨⟨h1, by omega⟩, ?_⟩, rfl⟩
          rw [show (m ++ [z], k - 1).2 = k - 1 from rfl, show (m ++ [z], k - 1).1 = m ++ [z] from rfl,
            ← hlen, List.eraseIdx_length_sub_one, ← colorSeq_dropLast]
          exact h2
      -- Step 4: induction on the dimension.
      have hIH : Odd (rainbowCells c (A.erase z)).card := by
        refine ih (A.erase z).card ?_ (A.erase z) c rfl
          (fun S hS hSA => hc S hS (hSA.trans (Finset.erase_subset _ _)))
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hz
      rw [← ZMod.natCast_eq_one_iff_odd, ← hstep1,
        ← Finset.card_filter_add_card_filter_not (s := S) (fun p => p.2 = k - 1)]
      push_cast
      rw [hmid, add_zero, htop, ZMod.natCast_eq_one_iff_odd]
      exact hIH

/-- **Sperner's lemma.**  Let `Δ(A)` be the simplex with vertex set `A`, barycentrically
subdivided; its cells are the maximal flags of faces of `Δ(A)`, encoded as orderings of
`A`.  For any Sperner colouring `c` (each barycentre `S` receives a colour `c S ∈ S`),
the number of rainbow cells is odd. -/
