/-
# Fullerene Pentagons
Category: Chemistry
Target: Chem.fullerene_pentagons
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fullerene Pentagons

A trivalent polyhedron all of whose faces are pentagons or hexagons has exactly 12 pentagons.
-/

namespace Chem

/-- Arithmetic core of the fullerene count: if `p` faces are pentagons and `h` faces are
hexagons, every vertex has degree `3`, and Euler's formula `V - E + F = 2` holds, then
`p = 12`. -/
theorem fullerene_pentagons_arith (V E F p h : ℕ)
    (euler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (trivalent : 2 * E = 3 * V)
    (face_count : p + h = F)
    (edge_count : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

/-- **Fullerene pentagon count.**

Let a polyhedron be given combinatorially by a finite vertex set `𝒱`, a finite edge set `ℰ`
and a finite face set `ℱ`, satisfying Euler's formula.  Assume:

* it is *trivalent*: each vertex lies on exactly `3` edges, so `2 * #ℰ = 3 * #𝒱`
  (each edge has two endpoints);
* every face is a pentagon or a hexagon, `size f ∈ {5, 6}`, and each edge lies on exactly two
  faces, so the face sizes sum to `2 * #ℰ`.

Then exactly `12` faces are pentagons. -/
theorem fullerene_pentagons {𝒱 ℰ ℱ : Type*}
    [Fintype 𝒱] [Fintype ℰ] [Fintype ℱ] [DecidableEq ℱ]
    (size : ℱ → ℕ)
    (euler : (Fintype.card 𝒱 : ℤ) - Fintype.card ℰ + Fintype.card ℱ = 2)
    (trivalent : 2 * Fintype.card ℰ = 3 * Fintype.card 𝒱)
    (pentagon_or_hexagon : ∀ f, size f = 5 ∨ size f = 6)
    (edge_faces : ∑ f, size f = 2 * Fintype.card ℰ) :
    ({f | size f = 5} : Finset ℱ).card = 12 := by
  classical
  set P : Finset ℱ := {f | size f = 5} with hP
  set H : Finset ℱ := {f | size f = 6} with hH
  -- the two sets partition all faces
  have hdisj : Disjoint P H := by
    simp only [hP, hH, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha hb
    omega
  have hunion : P ∪ H = Finset.univ := by
    ext f
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, hP, hH, Finset.mem_filter,
      true_and]
    exact pentagon_or_hexagon f
  have hcard : P.card + H.card = Fintype.card ℱ := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  -- the sum of face sizes splits accordingly
  have hsum : ∑ f, size f = 5 * P.card + 6 * H.card := by
    rw [← hunion, Finset.sum_union hdisj]
    have h1 : ∑ f ∈ P, size f = 5 * P.card := by
      rw [Finset.sum_congr rfl (fun f hf => by
        simpa [hP, Finset.mem_filter] using (Finset.mem_filter.mp hf).2)]
      simp [mul_comm]
    have h2 : ∑ f ∈ H, size f = 6 * H.card := by
      rw [Finset.sum_congr rfl (fun f hf => by
        simpa [hH, Finset.mem_filter] using (Finset.mem_filter.mp hf).2)]
      simp [mul_comm]
    rw [h1, h2]
  refine fullerene_pentagons_arith (Fintype.card 𝒱) (Fintype.card ℰ) (Fintype.card ℱ)
    P.card H.card euler trivalent hcard ?_
  rw [← hsum, edge_faces]

end Chem

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

