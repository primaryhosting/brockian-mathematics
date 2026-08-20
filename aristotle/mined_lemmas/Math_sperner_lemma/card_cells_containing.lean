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

lemma card_cells_containing {k v : ℕ} (hk : 0 < k) (hv : v ≤ k) :
    #{s ∈ intervalCells k | ({v} : Finset ℕ) ⊆ s} = if v = 0 ∨ v = k then 1 else 2 := by
  have hfil : {s ∈ intervalCells k | ({v} : Finset ℕ) ⊆ s}
      = ((Finset.range k).filter (fun j => v = j ∨ v = j + 1)).image
          (fun j => ({j, j + 1} : Finset ℕ)) := by
    rw [intervalCells, Finset.filter_image]
    congr 1
    refine Finset.filter_congr (fun j _ => ?_)
    simp only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ hab => pair_inj hab)]
  by_cases h0 : v = 0
  · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {0} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hset, Finset.card_singleton, if_pos (Or.inl h0)]
  · by_cases hkk : v = k
    · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {k - 1} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
      rw [hset, Finset.card_singleton, if_pos (Or.inr hkk)]
    · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {v - 1, v} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hset, Finset.card_pair (by omega), if_neg (by tauto)]

/-- The subdivided interval is a triangulation of the `1`-simplex; in particular the
hypotheses of `sperner_lemma` are satisfied by genuinely subdivided triangulations. -/
