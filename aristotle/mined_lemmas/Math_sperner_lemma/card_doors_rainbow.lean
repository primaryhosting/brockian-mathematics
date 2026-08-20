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

lemma card_doors_rainbow {s : Finset V} {c : V → ι} {I J : Finset ι} {i : ι} {n : ℕ}
    (hs : s.card = n + 2) (hI : I.card = n + 2) (hi : i ∈ I) (hJ : J = I.erase i)
    (himg : s.image c = I) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 1 := by
  rw [card_doors_eq s c J n hs]
  have hinj : Set.InjOn c s := Finset.injOn_of_card_image_eq (by rw [himg, hI, hs])
  have key : ∀ w ∈ s, ((s.erase w).image c = J ↔ c w = i) := by
    intro w hw
    rw [image_erase_injOn hinj hw, himg, hJ]
    exact Finset.erase_inj I (himg ▸ Finset.mem_image_of_mem c hw)
  have hset : {w ∈ s | (s.erase w).image c = J} = {w ∈ s | c w = i} :=
    Finset.filter_congr (fun w hw => by simp [key w hw])
  rw [hset, Finset.card_eq_one]
  have hmem : i ∈ s.image c := by rw [himg]; exact hi
  obtain ⟨v, hv, hcv⟩ := Finset.mem_image.mp hmem
  refine ⟨v, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨by simp [hv, hcv], ?_⟩
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hinj hx.1 hv (by rw [hx.2, hcv])

/-- If the colours of a cell are exactly `J` (so one colour is repeated), the cell has
exactly two facets with colour set `J`. -/
