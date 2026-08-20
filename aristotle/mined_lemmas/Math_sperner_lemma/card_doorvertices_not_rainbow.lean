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

lemma card_doorvertices_not_rainbow {s : Finset V} {c : V → ι} {F : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ F) (hcard : s.card = F.card) (hsub : s.image c ⊆ F) (hnr : s.image c ≠ F) :
    {v ∈ s | (s.erase v).image c = F.erase i₀}.card % 2 = 0 := by
  by_cases hF' : F.erase i₀ ⊆ s.image c
  · -- then `s.image c = F.erase i₀`, and there are exactly two doors
    have himg : s.image c = F.erase i₀ := by
      refine Finset.Subset.antisymm ?_ hF'
      intro i hi
      rcases eq_or_ne i i₀ with rfl | hii
      · exact absurd (Finset.Subset.antisymm hsub (fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact hi
          · exact hF' (Finset.mem_erase.mpr ⟨hji, hj⟩))) hnr
      · exact Finset.mem_erase.mpr ⟨hii, hsub hi⟩
    have hcards : (s.image c).card < s.card := by
      rw [himg, hcard, Finset.card_erase_of_mem hi₀]
      have : 0 < F.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    obtain ⟨u, hu, w, hw, huw, hcuw⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcards
        (fun x hx => Finset.mem_image_of_mem c hx)
    -- erasing either `u` or `w` does not change the image
    have himg_erase : ∀ (a b : V), a ∈ s → b ∈ s → a ≠ b → c a = c b →
        (s.erase a).image c = s.image c := by
      intro a b ha hb hab hcab
      refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _)) ?_
      intro i hi
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hi
      rcases eq_or_ne x a with rfl | hxa
      · exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩, hcab.symm⟩
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxa, hxs⟩, rfl⟩
    have himgu : (s.erase u).image c = s.image c := himg_erase u w hu hw huw hcuw
    have himgw : (s.erase w).image c = s.image c := himg_erase w u hw hu huw.symm hcuw.symm
    have hcardeu : ((s.erase u).image c).card = (s.erase u).card := by
      rw [himgu, himg, Finset.card_erase_of_mem hu, hcard, Finset.card_erase_of_mem hi₀]
    have hinju : ∀ x ∈ s.erase u, ∀ y ∈ s.erase u, c x = c y → x = y := by
      intro x hx y hy hxy
      exact Finset.injOn_of_card_image_eq hcardeu (Finset.mem_coe.mpr hx)
        (Finset.mem_coe.mpr hy) hxy
    have hudoor : (s.erase u).image c = F.erase i₀ := by rw [himgu, himg]
    have hwdoor : (s.erase w).image c = F.erase i₀ := by rw [himgw, himg]
    have hset : {v ∈ s | (s.erase v).image c = F.erase i₀} = {u, w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hvs, hv⟩
        by_contra hcon
        push_neg at hcon
        obtain ⟨hvu, hvw⟩ := hcon
        have hcv : c v ∈ (s.erase v).image c := by
          rw [hv, ← himg]; exact Finset.mem_image_of_mem c hvs
        obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp hcv
        obtain ⟨hxv, hxs⟩ := Finset.mem_erase.mp hx
        rcases eq_or_ne x u with hxu | hxu
        · refine hvw (hinju v (Finset.mem_erase.mpr ⟨hvu, hvs⟩) w
            (Finset.mem_erase.mpr ⟨huw.symm, hw⟩) ?_)
          rw [← hcx, hxu, hcuw]
        · exact hxv (hinju x (Finset.mem_erase.mpr ⟨hxu, hxs⟩) v
            (Finset.mem_erase.mpr ⟨hvu, hvs⟩) hcx)
      · intro h
        rcases h with h | h
        · subst h; exact ⟨hu, hudoor⟩
        · subst h; exact ⟨hw, hwdoor⟩
    rw [hset, Finset.card_pair huw]
  · -- no doors at all
    have hempty : {v ∈ s | (s.erase v).image c = F.erase i₀} = ∅ := by
      apply Finset.filter_false_of_mem
      intro v _ h
      exact hF' (h ▸ Finset.image_subset_image (Finset.erase_subset _ _))
    rw [hempty]
    simp

end Aux

/-! ### Sperner's lemma -/

namespace TriangulatedSimplex

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] (T : TriangulatedSimplex ι V)

