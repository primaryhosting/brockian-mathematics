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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

def bdry (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V)) : Finset (Finset V) :=
  Finset.univ.filter (fun F =>
    F.card = n + 1 ∧ (∀ v ∈ F, car v ⊆ Finset.range (n + 1)) ∧ Odd (cellMult T F))

/-- `IsSpernerTriangulation c car n T` is the combinatorial model of an `n`-simplex,
triangulated with cell set `T`, carrying a Sperner colouring `c`.

A vertex `v` has a colour `c v` and a *carrier* `car v`, the set of colours spanning the
smallest face of the big simplex containing `v`.  The conditions are:

* every cell has `n+1` vertices;
* (Sperner condition) `c v ∈ car v`, and `car v` is a set of colours of the big simplex;
* a face of a cell of size `n` lying in an odd number of cells is a boundary face, hence is
  contained in a proper face of the big simplex, i.e. misses some colour `i`;
* the induced triangulation of the face spanned by the colours `0, …, n-1` is again a Sperner
  triangulation, of dimension `n-1`;
* in dimension `0`, the triangulation is a single vertex, coloured `0`.

See `Math.isSpernerTriangulation_std`, `Math.segment_isSpernerTriangulation` and
`Math.triangle_isSpernerTriangulation` for instances of this notion. -/
