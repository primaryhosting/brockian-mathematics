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

def IsTriang : ℕ → Finset ι → (V → Finset ι) → Finset (Finset V) → Prop
  | 0, I, car, cells =>
      I.card = 1 ∧ cells.card = 1 ∧ (∀ s ∈ cells, s.card = 1) ∧
        (∀ s ∈ cells, ∀ v ∈ s, car v ⊆ I)
  | (m + 1), I, car, cells =>
      I.card = m + 2 ∧
      (∀ s ∈ cells, s.card = m + 2) ∧
      (∀ s ∈ cells, ∀ v ∈ s, car v ⊆ I) ∧
      (∀ f ∈ facets (m + 1) cells,
        #{s ∈ cells | f ⊆ s} = if f.biUnion car = I then 2 else 1) ∧
      (∀ i ∈ I, IsTriang m (I.erase i) car (faceCells (m + 1) car (I.erase i) cells))

/-- The rainbow cells of a colouring: those whose vertex colours are exactly the labels `I`. -/
