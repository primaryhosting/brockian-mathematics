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

lemma isClosed_sector2 (φ : ℝ) : IsClosed (sector2 φ) := by
  have h1 : IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} := isClosed_le (by fun_prop) (by fun_prop)
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le (by fun_prop) (by fun_prop)
  have h3 : IsClosed {p : ℝ × ℝ | 0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

