/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Finset

namespace Math

/-!
## Combinatorial setting

A triangulation of an `m`-dimensional simplex whose vertices (of the big simplex) are
labelled by a finite set `I` of labels (`I.card = m + 1`) is described combinatorially by:

* a type `V` of vertices of the triangulation;
* a *carrier* map `car : V → Finset ι`, sending a vertex `v` to the set of labels spanning
  the smallest face of the big simplex containing `v` (the support of the barycentric
  coordinates of `v`);
* a finite family `cells : Finset (Finset V)` of maximal cells, each with `m + 1` vertices.

The defining combinatorial properties of a triangulation (a "pseudomanifold with boundary"
whose boundary is the triangulated boundary of the simplex) are:

* every `m`-element face (*facet*) of a cell lies in exactly two cells if it is interior,
  and in exactly one cell if it lies in a proper face of the big simplex (equivalently,
  the union of the carriers of its vertices is not all of `I`);
* for every label `i`, the facets lying in the face opposite to `i` form, with the same
  carrier map, a triangulation of that `(m-1)`-dimensional face.

This is `Math.IsTriang` below.  A *Sperner colouring* is a map `c : V → ι` with
`c v ∈ car v` for every vertex `v`, and a cell is *rainbow* when the colours of its
vertices are exactly the labels `I`.
-/

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- All `k`-element subsets of cells of `cells` (the *facets* when `k` is one less than the
cardinality of the cells). -/

lemma card_doors_double {s : Finset V} {c : V → ι} {J : Finset ι} {n : ℕ}
    (hs : s.card = n + 2) (hJ : J.card = n + 1) (himg : s.image c = J) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 2 := by
  rw [card_doors_eq s c J n hs]
  obtain ⟨u, hu, v, hv, huv, hcuv⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by omega : J.card < s.card)
      (fun x hx => by rw [← himg]; exact Finset.mem_image_of_mem c hx)
  have hkeep : ∀ a b : V, a ∈ s → b ∈ s → a ≠ b → c a = c b → (s.erase a).image c = J := by
    intro a b ha hb hab hcab
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      rw [← himg]
      exact Finset.mem_image_of_mem c (Finset.mem_of_mem_erase ht)
    · intro x hx
      rw [← himg] at hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : t = a
      · subst h
        exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩, hcab.symm⟩
      · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨h, ht⟩, rfl⟩
  have hother : ∀ w ∈ s, w ≠ u → w ≠ v → (s.erase w).image c ≠ J := by
    intro w hw hwu hwv
    have hu' : u ∈ (s.erase w).erase v :=
      Finset.mem_erase.mpr ⟨huv, Finset.mem_erase.mpr ⟨fun h => hwu h.symm, hu⟩⟩
    have hv' : v ∈ s.erase w := Finset.mem_erase.mpr ⟨fun h => hwv h.symm, hv⟩
    have heq : (s.erase w).image c = ((s.erase w).erase v).image c := by
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
        by_cases h : t = v
        · subst h
          exact Finset.mem_image.mpr ⟨u, hu', hcuv⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨h, ht⟩, rfl⟩
      · exact Finset.image_subset_image (Finset.erase_subset _ _)
    intro hcon
    have hcard : ((s.erase w).erase v).card = n := by
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hw, hs]; omega
    have hle := Finset.card_image_le (s := ((s.erase w).erase v)) (f := c)
    rw [← heq, hcon, hJ, hcard] at hle
    omega
  have hset : {w ∈ s | (s.erase w).image c = J} = {u, v} := by
    apply Finset.Subset.antisymm
    · intro w hw
      simp only [Finset.mem_filter] at hw
      by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      exact hother w hw.1 hcon.1 hcon.2 hw.2
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hu, hkeep w v hu hv huv hcuv⟩
      · exact Finset.mem_filter.mpr ⟨hv, hkeep w u hv hu (Ne.symm huv) hcuv.symm⟩
  rw [hset, Finset.card_pair huv]

omit [DecidableEq V] in
/-- A cell whose colour set is neither `I` nor `J = I.erase i` has no facet with colour
set `J`. -/
