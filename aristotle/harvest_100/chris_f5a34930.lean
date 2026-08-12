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

namespace Chem

/-- **Fullerene / trivalent polyhedron count of pentagons.**

A convex (equivalently, planar, connected) polyhedron with `V` vertices, `E` edges and
`F` faces satisfies Euler's formula `V - E + F = 2`.  Assume moreover that it is
*trivalent*: every vertex lies on exactly three edges, so summing vertex degrees gives
`3 * V = 2 * E`; and that every face is a pentagon or a hexagon, say `p` pentagons and
`h` hexagons, so `F = p + h` and summing face degrees gives `5 * p + 6 * h = 2 * E`.

Then there are exactly `12` pentagons, whatever the number of hexagons. -/
theorem fullerene_pentagons_count
    (V E F p h : ℕ)
    (hEuler : (V : ℤ) - E + F = 2)
    (htrivalent : 3 * V = 2 * E)
    (hfaces : F = p + h)
    (hdeg : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-- **Fullerene / trivalent polyhedron: exactly 12 pentagonal faces.**

Here the faces are indexed by a finite type `Face`, and `size f` is the number of edges
(equivalently vertices) of the face `f`.  The hypotheses are:

* `hsize`: every face is a pentagon or a hexagon;
* `hEuler`: Euler's formula `V - E + F = 2` for the polyhedron, `F` being the number of faces;
* `htrivalent`: every vertex meets exactly three edges (`3 * V = 2 * E`);
* `hdeg`: each edge lies on exactly two faces, i.e. the face sizes sum to `2 * E`.

Conclusion: exactly `12` faces are pentagons. -/
theorem fullerene_pentagons
    {Face : Type*} [Fintype Face] [DecidableEq Face] (size : Face → ℕ) (V E : ℕ)
    (hsize : ∀ f, size f = 5 ∨ size f = 6)
    (hEuler : (V : ℤ) - E + Fintype.card Face = 2)
    (htrivalent : 3 * V = 2 * E)
    (hdeg : ∑ f, size f = 2 * E) :
    (Finset.univ.filter fun f => size f = 5).card = 12 := by
  classical
  set P : Finset Face := Finset.univ.filter fun f => size f = 5 with hP
  set H : Finset Face := Finset.univ.filter fun f => size f = 6 with hH
  have hdisj : Disjoint P H := by
    refine Finset.disjoint_left.mpr ?_
    intro f hf hf'
    simp only [hP, hH, Finset.mem_filter] at hf hf'
    omega
  have hunion : P ∪ H = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro f
    rcases hsize f with h5 | h6
    · exact Finset.mem_union_left _ (by simp [hP, h5])
    · exact Finset.mem_union_right _ (by simp [hH, h6])
  have hcard : P.card + H.card = Fintype.card Face := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hsum : ∑ f, size f = 5 * P.card + 6 * H.card := by
    rw [← hunion, Finset.sum_union hdisj]
    have h1 : ∑ f ∈ P, size f = 5 * P.card := by
      rw [Finset.sum_congr rfl (fun f hf => (Finset.mem_filter.mp hf).2)]
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have h2 : ∑ f ∈ H, size f = 6 * H.card := by
      rw [Finset.sum_congr rfl (fun f hf => (Finset.mem_filter.mp hf).2)]
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [h1, h2]
  exact fullerene_pentagons_count V E (Fintype.card Face) P.card H.card hEuler htrivalent
    hcard.symm (by omega)

end Chem

