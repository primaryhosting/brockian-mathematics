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

lemma isTriang_single (m : ℕ) (I : Finset ι) (hI : I.card = m + 1) :
    IsTriang m I (fun v => ({v} : Finset ι)) {I} := by
  induction m generalizing I with
  | zero =>
    refine ⟨hI, Finset.card_singleton _, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      rw [hs, hI]
    · intro s hs v hv x hx
      rw [Finset.mem_singleton] at hs hx
      rw [hs] at hv
      rwa [hx]
  | succ n ih =>
    have hfacet : ∀ f ∈ facets (n + 1) ({I} : Finset (Finset ι)), f ⊆ I ∧ f.card = n + 1 := by
      intro f hf
      obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
      rw [Finset.mem_singleton] at ht
      rw [Finset.mem_powersetCard, ht] at hft
      exact hft
    refine ⟨hI, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      rw [hs, hI]
    · intro s hs v hv x hx
      rw [Finset.mem_singleton] at hs hx
      rw [hs] at hv
      rwa [hx]
    · intro f hf
      obtain ⟨hfsub, hfcard⟩ := hfacet f hf
      have hne : f.biUnion (fun v => ({v} : Finset ι)) ≠ I := by
        rw [Finset.biUnion_singleton_eq_self]
        intro hcon
        rw [hcon, hI] at hfcard
        omega
      rw [if_neg hne]
      have : ({I} : Finset (Finset ι)).filter (fun s => f ⊆ s) = {I} :=
        Finset.filter_true_of_mem (by intro s hs; rw [Finset.mem_singleton] at hs; rwa [hs])
      rw [this, Finset.card_singleton]
    · intro i hi
      have hcard : (I.erase i).card = n + 1 := by
        rw [Finset.card_erase_of_mem hi, hI]; omega
      have hfc : faceCells (n + 1) (fun v => ({v} : Finset ι)) (I.erase i) {I}
          = {I.erase i} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          rw [Finset.biUnion_singleton_eq_self] at hbi
          exact Finset.eq_of_subset_of_card_le hbi (by rw [hcard, (hfacet f hf).2])
        · rintro rfl
          refine ⟨?_, by rw [Finset.biUnion_singleton_eq_self]⟩
          exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_singleton_self I,
            Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, hcard⟩⟩
      rw [hfc]
      exact ih (I.erase i) hcard

/-- Sperner's lemma applied to the coarsest triangulation: the identity colouring of the
single cell is a Sperner colouring with exactly one rainbow cell. -/
example (m : ℕ) (I : Finset ι) (hI : I.card = m + 1) :
    Odd #(rainbowCells I (id : ι → ι) {I}) :=
  sperner_lemma (isTriang_single m I hI) id (fun v => Finset.mem_singleton_self v)


/-! ### A genuinely subdivided example

The interval `[0, k]` subdivided into the `k` cells `{j, j+1}`, `j < k`, with the two
endpoints `0` and `k` carrying the two vertices of the `1`-simplex.  This shows that
`IsTriang` is satisfied by honest subdivisions, not only by the coarsest one. -/

/-- The cells of the subdivided interval. -/
