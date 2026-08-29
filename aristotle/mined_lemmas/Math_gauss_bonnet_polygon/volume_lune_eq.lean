/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.SphericalWedge

/-!
# Gauss Bonnet Polygon

Category: Pure Mathematics.  Target: `Math.gauss_bonnet_polygon`.

## Overview

We prove Girard's theorem (the Gauss–Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the three interior angles of a spherical triangle equals `π` plus the
area of the triangle.

The area of a region `S` of the unit sphere in `ℝ³` is defined as three times the Lebesgue
volume of the cone over `S` with apex the origin (this is the standard normalisation: the
cone over the whole sphere is the unit ball, of volume `4π/3`, giving total area `4π`).

The proof is the classical "lune" argument.  The three great circles through the pairs of
vertices cut the sphere into eight triangles; each of the three lunes containing the
triangle `T` decomposes as `T` together with one of the neighbouring triangles.
-/

open MeasureTheory Metric Real Set InnerProductGeometry Pointwise

noncomputable section

namespace GaussBonnet

/-! ### Step 4: the normals to the sides of a spherical triangle -/

/-- The interior angle at the vertex `u` of the spherical triangle with vertices `u`, `v`, `w`:
the angle between the tangent directions at `u` of the two geodesics from `u` to `v` and
from `u` to `w`. -/

lemma volume_lune_eq (cu cv cw : E3) (hcu : cu ≠ 0) (hcv : cv ≠ 0) (hcw : cw ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ (inner ℝ cv x : ℝ) ∧ 0 ≤ (inner ℝ cw x : ℝ)}
      = volume (osec cu cv cw (true, true, true)) + volume (osec cu cv cw (false, true, true)) := by
  have hdisj : Disjoint (osec cu cv cw (true, true, true)) (osec cu cv cw (false, true, true)) :=
    osec_disjoint cu cv cw (by simp)
  rw [← measure_union hdisj (measurableSet_osec _ _ _ _)]
  refine volume_eq_of_sandwich (volume_triple_hyperplane cu cv cw hcu hcv hcw) ?_ ?_
  · rintro x (hx | hx) <;>
      exact ⟨hx.1, by simpa [sgn] using hx.2.2.1.le, by simpa [sgn] using hx.2.2.2.le⟩
  · rintro x ⟨hn, h2, h3⟩
    by_cases h1 : inner ℝ cu x = (0 : ℝ)
    · exact Or.inr (Or.inl (Or.inl h1))
    by_cases h2' : inner ℝ cv x = (0 : ℝ)
    · exact Or.inr (Or.inl (Or.inr h2'))
    by_cases h3' : inner ℝ cw x = (0 : ℝ)
    · exact Or.inr (Or.inr h3')
    have hp2 : 0 < (inner ℝ cv x : ℝ) := lt_of_le_of_ne h2 (Ne.symm h2')
    have hp3 : 0 < (inner ℝ cw x : ℝ) := lt_of_le_of_ne h3 (Ne.symm h3')
    rcases lt_or_gt_of_ne h1 with h | h
    · exact Or.inl (Or.inr ⟨hn, by simp [sgn]; linarith, by simpa [sgn] using hp2,
        by simpa [sgn] using hp3⟩)
    · exact Or.inl (Or.inl ⟨hn, by simpa [sgn] using h, by simpa [sgn] using hp2,
        by simpa [sgn] using hp3⟩)

end GaussBonnet

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

import Mathlib

/-!
# Spherical wedges

Supporting material for the Gauss-Bonnet theorem for spherical polygons.

## Overview

We prove Girard's theorem (the Gauss–Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the three interior angles of a spherical triangle equals `π` plus the
area of the triangle.

The area of a region `S` of the unit sphere in `ℝ³` is defined as three times the Lebesgue
volume of the cone over `S` with apex the origin (this is the standard normalisation:
the cone over the whole sphere is the unit ball, of volume `4π/3`, giving total area `4π`).

The proof is the classical "lune" argument.  The three great circles through the pairs of
vertices cut the sphere into eight triangles; each of the three lunes containing the
triangle `T` decomposes as `T` together with one of the neighbouring triangles.
-/

open MeasureTheory Metric Real Set InnerProductGeometry Pointwise

noncomputable section

namespace GaussBonnet

/-- Euclidean three-space, the ambient space for the unit sphere. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### Step 1: the area of a planar circular sector -/

/-- The planar sector of the closed unit disc cut out by the two half-planes
`0 ≤ x` and `0 ≤ x cos φ + y sin φ`.  For `0 < φ < π` this is a sector of angle `π - φ`. -/
