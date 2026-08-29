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

private lemma box_lint (a b : ℝ) :
    ∫⁻ p in (Ioc (0 : ℝ) 1) ×ˢ (Icc a b), ENNReal.ofReal p.1 = ENNReal.ofReal ((b - a) / 2) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  rw [lintegral_mul_const _ (by fun_prop)]
  have h2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal x = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le (by norm_num)]
      simp
    · exact continuous_id.integrableOn_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using le_of_lt hx.1
  rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
  rcases le_total a b with h | h
  · congr 1; ring
  · rw [ENNReal.ofReal_eq_zero.2 (by nlinarith), ENNReal.ofReal_eq_zero.2 (by linarith)]

/-- The area of the planar sector of angle `π - φ` in the unit disc is `(π - φ)/2`. -/
