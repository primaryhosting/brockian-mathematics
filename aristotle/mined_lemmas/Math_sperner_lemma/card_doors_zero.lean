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

lemma card_doors_zero {s : Finset V} {c : V → ι} {I J : Finset ι} {i : ι} {n : ℕ}
    (hi : i ∈ I) (hJ : J = I.erase i) (hsub : s.image c ⊆ I)
    (h1 : s.image c ≠ I) (h2 : s.image c ≠ J) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf
  rw [Finset.mem_powersetCard] at hf
  intro hcon
  have hJsub : J ⊆ s.image c := by
    rw [← hcon]; exact Finset.image_subset_image hf.1
  by_cases hii : i ∈ s.image c
  · exact h1 (Finset.Subset.antisymm hsub (by
      rw [← Finset.insert_erase hi, ← hJ, Finset.insert_subset_iff]
      exact ⟨hii, hJsub⟩))
  · refine h2 (Finset.Subset.antisymm ?_ hJsub)
    intro x hx
    rw [hJ, Finset.mem_erase]
    exact ⟨fun h => hii (h ▸ hx), hsub hx⟩

omit [DecidableEq V] in
/-- Double counting: the number of incident pairs computed in the two possible orders. -/
