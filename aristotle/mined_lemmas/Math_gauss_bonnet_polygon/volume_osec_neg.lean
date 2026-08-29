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

lemma volume_osec_neg (cu cv cw : E3) (s : Bool × Bool × Bool) :
    volume (osec cu cv cw (!s.1, !s.2.1, !s.2.2)) = volume (osec cu cv cw s) := by
  have hset : osec cu cv cw (!s.1, !s.2.1, !s.2.2) = (fun x : E3 => -x) ⁻¹' osec cu cv cw s := by
    ext x
    simp only [osec, mem_setOf_eq, mem_preimage, norm_neg, inner_neg_right, sgn_not]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩
  rw [hset, (Measure.measurePreserving_neg volume).measure_preimage
    (measurableSet_osec cu cv cw s).nullMeasurableSet]

/-- If `B ⊆ A ⊆ B ∪ N` with `N` null, then `A` and `B` have the same volume. -/
