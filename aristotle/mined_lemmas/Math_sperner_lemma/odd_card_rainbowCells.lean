import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Sperner's lemma

We formalise the classical combinatorial content of Sperner's lemma.

A *triangulated simplex* is described combinatorially: the vertices of the simplex are
labelled by a type `ι` (for the `n`-simplex, `ι = Fin (n+1)`), and a triangulation consists
of a finite abstract simplicial complex `faces` of *vertices* (of type `V`) together with,
for each vertex `v`, the *carrier* `carrier v ⊆ ι`: the (unique) minimal face of the big
simplex containing `v`.

For a face `t` of the triangulation, its *span* `span t = ⋃ {carrier v | v ∈ t}` is the
smallest face of the big simplex containing `t`.  For `F ⊆ ι`, the cells of the sub-simplex
spanned by `F` are the faces `s` with `span s ⊆ F` and `s.card = F.card`; these are exactly
the top-dimensional simplices of the induced triangulation of that face of the big simplex.

The single geometric input is then the *door axiom*: if `t` is a face lying inside the
sub-simplex `F` and of codimension one there, then `t` is contained in exactly two cells of
`F` when `t` is interior to `F` (i.e. `span t = F`), and in exactly one cell of `F` when `t`
lies in the boundary of `F` (i.e. `span t ⊊ F`).  This is the standard combinatorial
abstraction of "triangulation of a simplex"; see `Math.trivialTriangulation` and
`Math.subdividedSegment` below for instances.

A *Sperner colouring* assigns to each vertex `v` a colour `c v ∈ carrier v`; a cell of `F`
is *rainbow* if it carries all the colours of `F`.  Sperner's lemma says the number of
rainbow cells is odd. -/

/-- A combinatorial triangulation of the simplex with vertex set `ι`, whose vertices are of
type `V`. -/
structure TriangulatedSimplex (ι V : Type*) [DecidableEq ι] [DecidableEq V] where
  /-- The faces of the triangulation. -/
  faces : Finset (Finset V)
  /-- The carrier of a vertex: the minimal face of the big simplex containing it. -/
  carrier : V → Finset ι
  /-- The empty face belongs to the complex. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- The set of faces is closed under passing to subsets. -/
  down_closed : ∀ ⦃s : Finset V⦄, s ∈ faces → ∀ ⦃t : Finset V⦄, t ⊆ s → t ∈ faces
  /-- The door axiom: a codimension-one face `t` of the sub-simplex spanned by `F` lies in
  exactly two cells of `F` if it is interior to `F`, and in exactly one cell of `F` if it
  lies on the boundary of `F`. -/
  door : ∀ (F : Finset ι) (t : Finset V), t ∈ faces → t.card + 1 = F.card →
      t.biUnion carrier ⊆ F →
      {s ∈ faces | s.card = F.card ∧ s.biUnion carrier ⊆ F ∧ t ⊆ s}.card
        = if t.biUnion carrier = F then 2 else 1

namespace TriangulatedSimplex

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] (T : TriangulatedSimplex ι V)

/-- The span of a face: the smallest face of the big simplex containing it. -/

theorem odd_card_rainbowCells {c : V → ι} (hc : T.IsSpernerColoring c) (F : Finset ι) :
    Odd (T.rainbowCells c F).card := by
  induction F using Finset.strongInduction with
  | _ F ih =>
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · -- base case: the unique cell of the empty simplex is the empty face, which is rainbow
    have hrb : T.rainbowCells c ∅ = {∅} := by
      ext s
      simp only [rainbowCells, cells, Finset.mem_filter, Finset.mem_singleton,
        Finset.card_empty]
      constructor
      · rintro ⟨⟨-, hs, -⟩, -⟩
        exact Finset.card_eq_zero.mp hs
      · rintro rfl
        exact ⟨⟨T.empty_mem, rfl, by simp [span]⟩, by simp⟩
    rw [hrb]
    simp
  · -- induction step
    set F' : Finset ι := F.erase i₀ with hF'
    have hF'sub : F' ⊂ F := Finset.erase_ssubset hi₀
    have hF'card : F'.card + 1 = F.card := by
      rw [hF', Finset.card_erase_of_mem hi₀]
      have : 0 < F.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    -- the set of doors
    set D : Finset (Finset V) :=
      {t ∈ T.faces | t.card = F'.card ∧ T.span t ⊆ F ∧ t.image c = F'} with hD
    have hmemD : ∀ t : Finset V,
        t ∈ D ↔ (t ∈ T.faces ∧ t.card = F'.card ∧ T.span t ⊆ F ∧ t.image c = F') := by
      intro t; simp [hD]
    -- first count: over cells
    have hcount1 : ((∑ s ∈ T.cells F, {t ∈ D | t ⊆ s}.card : ℕ) : ZMod 2)
        = ((T.rainbowCells c F).card : ZMod 2) := by
      have hterm : ∀ s ∈ T.cells F,
          (({t ∈ D | t ⊆ s}.card : ℕ) : ZMod 2) = (if s.image c = F then 1 else 0) := by
        intro s hs
        rw [T.mem_cells_iff] at hs
        obtain ⟨hsf, hscard, hspan⟩ := hs
        have hsub : s.image c ⊆ F := (T.image_subset_span hc s).trans hspan
        have hkey : {t ∈ D | t ⊆ s}.card
            = {v ∈ s | (s.erase v).image c = F'}.card := by
          refine card_doorset (k := F'.card) (by omega) (fun t => t.image c = F') ?_
          intro t hts
          rw [hmemD]
          constructor
          · rintro ⟨-, h1, -, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨T.down_closed hsf hts, h1, (T.span_mono hts).trans hspan, h2⟩
        rw [hkey]
        by_cases hrb : s.image c = F
        · rw [if_pos hrb, card_doorvertices_rainbow hi₀ hscard hrb]
          norm_num
        · rw [if_neg hrb]
          exact ZMod.natCast_eq_zero_iff_even.mpr
            (Nat.even_iff.mpr (card_doorvertices_not_rainbow hi₀ hscard hsub hrb))
      rw [Nat.cast_sum, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const,
        Finset.sum_const]
      simp only [mul_zero, add_zero, nsmul_eq_mul, mul_one]
      rfl
    -- second count: over doors
    have hcount2 : ((∑ t ∈ D, {s ∈ T.cells F | t ⊆ s}.card : ℕ) : ZMod 2)
        = ((T.rainbowCells c F').card : ZMod 2) := by
      have hterm : ∀ t ∈ D,
          (({s ∈ T.cells F | t ⊆ s}.card : ℕ) : ZMod 2) = (if T.span t = F' then 1 else 0) := by
        intro t ht
        rw [hmemD] at ht
        obtain ⟨htf, htcard, htspan, htimg⟩ := ht
        have hdoor : {s ∈ T.faces | s.card = F.card ∧ T.span s ⊆ F ∧ t ⊆ s}.card
            = if T.span t = F then 2 else 1 := T.door F t htf (by omega) htspan
        have hfilter : {s ∈ T.cells F | t ⊆ s}
            = {s ∈ T.faces | s.card = F.card ∧ T.span s ⊆ F ∧ t ⊆ s} := by
          simp [cells, Finset.filter_filter, and_assoc]
        rw [hfilter, hdoor]
        -- `F' ⊆ span t ⊆ F`, so `span t` is either `F'` or `F`
        have hF'sub' : F' ⊆ T.span t := by
          rw [← htimg]; exact T.image_subset_span hc t
        by_cases hst : T.span t = F
        · rw [if_pos hst, if_neg (by rw [hst]; exact fun h => hF'sub.ne h.symm)]
          decide
        · rw [if_neg hst]
          have hspF' : T.span t = F' := by
            refine Finset.Subset.antisymm ?_ hF'sub'
            intro i hi
            rcases eq_or_ne i i₀ with rfl | hii
            · refine absurd (Finset.Subset.antisymm htspan (fun j hj => ?_)) hst
              rcases eq_or_ne j i with rfl | hji
              · exact hi
              · exact hF'sub' (Finset.mem_erase.mpr ⟨hji, hj⟩)
            · exact Finset.mem_erase.mpr ⟨hii, htspan hi⟩
          rw [if_pos hspF']
          norm_num
      -- the doors with span `F'` are exactly the rainbow cells of `F'`
      have hsets : {t ∈ D | T.span t = F'} = T.rainbowCells c F' := by
        ext t
        simp only [Finset.mem_filter, hmemD, rainbowCells, cells, Finset.mem_filter]
        constructor
        · rintro ⟨⟨htf, htcard, -, htimg⟩, hspan⟩
          exact ⟨⟨htf, htcard, by rw [hspan]⟩, htimg⟩
        · rintro ⟨⟨htf, htcard, hspan⟩, htimg⟩
          have hF'sub' : F' ⊆ T.span t := by rw [← htimg]; exact T.image_subset_span hc t
          exact ⟨⟨htf, htcard, hspan.trans hF'sub.subset, htimg⟩,
            Finset.Subset.antisymm hspan hF'sub'⟩
      rw [Nat.cast_sum, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const,
        Finset.sum_const]
      simp only [mul_zero, add_zero, nsmul_eq_mul, mul_one]
      rw [hsets]
    -- combine
    have hswap : ∑ s ∈ T.cells F, {t ∈ D | t ⊆ s}.card
        = ∑ t ∈ D, {s ∈ T.cells F | t ⊆ s}.card :=
      sum_card_filter_comm (fun s t => t ⊆ s)
    have hcong : ((T.rainbowCells c F).card : ZMod 2) = ((T.rainbowCells c F').card : ZMod 2) := by
      rw [← hcount1, ← hcount2, hswap]
    have hodd' := ih F' hF'sub
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd' ⊢
    rw [hcong]
    exact hodd'

end TriangulatedSimplex

/-- **Sperner's lemma.**  For every Sperner colouring of a combinatorially triangulated
simplex, the number of rainbow cells is odd. -/
