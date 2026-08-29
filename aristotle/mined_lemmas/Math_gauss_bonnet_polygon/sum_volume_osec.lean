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

lemma sum_volume_osec (cu cv cw : E3) (hcu : cu ≠ 0) (hcv : cv ≠ 0) (hcw : cw ≠ 0) :
    ∑ s : Bool × Bool × Bool, volume (osec cu cv cw s) = ENNReal.ofReal (π * 4 / 3) := by
  have hball : volume (⋃ s, osec cu cv cw s) = volume (closedBall (0 : E3) 1) := by
    refine (volume_eq_of_sandwich (volume_triple_hyperplane cu cv cw hcu hcv hcw) ?_ ?_).symm
    · exact iUnion_subset fun s => osec_subset_ball cu cv cw s
    · intro x hx
      rw [mem_closedBall_zero_iff] at hx
      by_cases h1 : inner ℝ cu x = (0 : ℝ)
      · exact Or.inr (Or.inl (Or.inl h1))
      by_cases h2 : inner ℝ cv x = (0 : ℝ)
      · exact Or.inr (Or.inl (Or.inr h2))
      by_cases h3 : inner ℝ cw x = (0 : ℝ)
      · exact Or.inr (Or.inr h3)
      exact Or.inl (mem_iUnion.2 ⟨(decide (0 < inner ℝ cu x), decide (0 < inner ℝ cv x),
        decide (0 < inner ℝ cw x)), hx, sgn_decide h1, sgn_decide h2, sgn_decide h3⟩)
  rw [measure_iUnion (osec_disjoint cu cv cw) (measurableSet_osec cu cv cw),
    tsum_fintype] at hball
  rw [hball, EuclideanSpace.volume_closedBall_fin_three]
  simp

/-- The lune obtained by dropping the first constraint splits into two sectors. -/
