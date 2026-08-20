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

lemma isTriang_interval (k : ℕ) (hk : 0 < k) :
    IsTriang 1 ({0, 1} : Finset ℕ) (intervalCar k) (intervalCells k) := by
  have hcells : ∀ s ∈ intervalCells k, ∃ j < k, s = {j, j + 1} := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  have hcarsub : ∀ v : ℕ, intervalCar k v ⊆ ({0, 1} : Finset ℕ) := by
    intro v
    by_cases h0 : v = 0
    · rw [h0, intervalCar_zero]; decide
    · by_cases hkk : v = k
      · rw [hkk, intervalCar_top hk]; decide
      · rw [intervalCar_mid h0 hkk]
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := hcells s hs
    rw [Finset.card_pair (by omega)]
  · intro s _ v _
    exact hcarsub v
  · intro f hf
    obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
    rw [card_cells_containing hk hv, Finset.singleton_biUnion]
    by_cases h0 : v = 0
    · rw [if_pos (Or.inl h0), h0, intervalCar_zero, if_neg (by decide)]
    · by_cases hkk : v = k
      · rw [if_pos (Or.inr hkk), hkk, intervalCar_top hk, if_neg (by decide)]
      · rw [if_neg (by tauto), intervalCar_mid h0 hkk, if_pos rfl]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · have hJ : ({0, 1} : Finset ℕ).erase 0 = {1} := by decide
      rw [hJ]
      have hfc : faceCells 1 (intervalCar k) {1} (intervalCells k) = {{k}} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
          rw [Finset.singleton_biUnion] at hbi
          by_cases h0 : v = 0
          · rw [h0, intervalCar_zero] at hbi
            exact absurd (hbi (by decide : (0 : ℕ) ∈ ({0} : Finset ℕ))) (by decide)
          · by_cases hkk : v = k
            · rw [hkk]
            · rw [intervalCar_mid h0 hkk] at hbi
              exact absurd (hbi (by decide : (0 : ℕ) ∈ ({0, 1} : Finset ℕ))) (by decide)
        · rintro rfl
          refine ⟨(mem_facets_interval hk).mpr ⟨k, le_refl k, rfl⟩, ?_⟩
          rw [Finset.singleton_biUnion, intervalCar_top hk]
      rw [hfc]
      refine ⟨by decide, Finset.card_singleton _, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.card_singleton]
      · intro s hs v hv
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.mem_singleton] at hv
        rw [hv, intervalCar_top hk]
    · have hJ : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
      rw [hJ]
      have hfc : faceCells 1 (intervalCar k) {0} (intervalCells k) = {{0}} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
          rw [Finset.singleton_biUnion] at hbi
          by_cases h0 : v = 0
          · rw [h0]
          · by_cases hkk : v = k
            · rw [hkk, intervalCar_top hk] at hbi
              exact absurd (hbi (by decide : (1 : ℕ) ∈ ({1} : Finset ℕ))) (by decide)
            · rw [intervalCar_mid h0 hkk] at hbi
              exact absurd (hbi (by decide : (1 : ℕ) ∈ ({0, 1} : Finset ℕ))) (by decide)
        · rintro rfl
          refine ⟨(mem_facets_interval hk).mpr ⟨0, by omega, rfl⟩, ?_⟩
          rw [Finset.singleton_biUnion, intervalCar_zero]
      rw [hfc]
      refine ⟨by decide, Finset.card_singleton _, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.card_singleton]
      · intro s hs v hv
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.mem_singleton] at hv
        rw [hv, intervalCar_zero]

/-- Sperner's lemma in dimension one: for any colouring of the vertices `0, …, k` of the
subdivided interval with `c 0 = 0` and `c k = 1` (equivalently, `c v ∈ intervalCar k v`),
an odd number of the subintervals `{j, j+1}` are rainbow. -/
