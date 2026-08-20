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

set_option grind.warning false

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

def subComplex (K : Finset (Finset V)) (carr : V → Finset ℕ) (B : Finset ℕ) (k : ℕ) :
    Finset (Finset V) :=
  (facets K k).filter (fun f => f.biUnion carr ⊆ B)

/-- Combinatorial description of a triangulation of the simplex with vertex set `A`
(`A.card = n+1`, so `n` is the dimension).

* `K` is the finite set of top-dimensional cells, each an `(n+1)`-element set of vertices;
* `carr v` is the (nonempty) face of the simplex carrying the vertex `v`, so `carr v ⊆ A`;
* every codimension-one face `f` of a cell lies in exactly two cells if it is interior
  (equivalently, its vertices together span the whole simplex, `f.biUnion carr = A`) and in
  exactly one cell if it lies on the boundary;
* for each vertex `a` of the simplex, the faces carried by the opposite facet `A.erase a`
  form a triangulation of that facet. -/
