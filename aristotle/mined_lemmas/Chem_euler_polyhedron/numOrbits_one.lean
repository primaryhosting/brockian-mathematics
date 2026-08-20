import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

lemma numOrbits_one : numOrbits (1 : Perm ι) = Fintype.card ι := by
  classical
  have : Nat.card (Quotient (SameCycle.setoid (1 : Perm ι))) = Nat.card ι := by
    refine Nat.card_congr (Equiv.ofBijective (fun q => q.out) ?_)
    constructor
    · intro q q' hqq'
      have := congrArg (Quotient.mk (SameCycle.setoid (1 : Perm ι))) hqq'
      simpa using this
    · intro a
      refine ⟨Quotient.mk (SameCycle.setoid (1 : Perm ι)) a, ?_⟩
      have : (Quotient.mk (SameCycle.setoid (1 : Perm ι))
          (Quotient.mk (SameCycle.setoid (1 : Perm ι)) a).out) =
          Quotient.mk (SameCycle.setoid (1 : Perm ι)) a := Quotient.out_eq _
      rw [quotient_eq_iff_sameCycle] at this
      obtain ⟨i, hi⟩ := this
      simpa using hi
  rw [numOrbits, this, Nat.card_eq_fintype_card]

end Polyhedron

import RequestProject.OrbitCount

/-!
# Combinatorial maps on the sphere and Euler's polyhedron formula

A *combinatorial map* (rotation system) on a finite set `D` of *darts* consists of two
permutations:

* `s` (the *vertex permutation*): its orbits on `D` are the vertices, `s` rotating the darts
  around a vertex in the cyclic order given by the embedding;
* `a` (the *edge permutation*): a fixed-point-free involution on `D`, whose orbits (pairs of
  darts) are the edges.

The *faces* are then the orbits of `a * s`.  This is the standard encoding of a graph embedded
in an oriented surface; the surface is a sphere exactly when the map can be built up, starting
from a single edge, by repeatedly

* attaching a new pendant edge at a corner of the map (`pendant`), or
* drawing a new edge between two distinct corners lying on a common face (`chord`),

which is the content of the inductive predicate `IsSphericalMap` below.  The boundary complex of
a convex polyhedron (for instance a fullerene cage) yields such a map, its darts being the
(edge, endpoint) incidences.

The main theorem `Chem.euler_polyhedron` states Euler's formula `V - E + F = 2` for these maps.
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `IsSphericalMap D s a` says that the pair of permutations `(s, a)`, supported on the finite
set of darts `D`, is a combinatorial map of the sphere: it can be obtained from a single edge by
repeatedly attaching a pendant edge at a corner, or joining two distinct corners of a common
face by a new edge.  Here `s` encodes the cyclic order of the darts around each vertex and `a`
is the fixed-point-free involution pairing the two darts of each edge. -/
inductive IsSphericalMap : Finset ι → Perm ι → Perm ι → Prop
  /-- The map consisting of a single edge: two vertices, one edge and one face. -/
  | base {d₀ d₁ : ι} (h : d₀ ≠ d₁) : IsSphericalMap {d₀, d₁} 1 (swap d₀ d₁)
  /-- Attach a new edge with a new endpoint (a new vertex `y`) at the corner `d`. -/
  | pendant {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) {d x y : ι}
      (hd : d ∈ D) (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
      IsSphericalMap (insert x (insert y D)) (s * swap d x) (a * swap x y)
  /-- Join the two distinct corners `d` and `e` of a common face by a new edge. -/
  | chord {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) {d e x y : ι}
      (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) (hface : (a * s).SameCycle d e)
      (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
      IsSphericalMap (insert x (insert y D)) (s * swap d x * swap e y) (a * swap x y)

/-! ### Two permutation identities describing the effect of the moves on the faces -/

omit [Fintype ι] in
/-- Attaching a pendant edge inserts the two new darts into one face, leaving the number of
faces unchanged. -/
