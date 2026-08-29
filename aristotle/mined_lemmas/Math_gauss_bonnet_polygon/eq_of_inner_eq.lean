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

lemma eq_of_inner_eq {u v w y y' : E3} (hind : LinearIndependent ℝ ![u, v, w])
    (h1 : inner ℝ y u = (inner ℝ y' u : ℝ)) (h2 : inner ℝ y v = (inner ℝ y' v : ℝ))
    (h3 : inner ℝ y w = (inner ℝ y' w : ℝ)) : y = y' := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  have hbas : ⇑(basisOfLinearIndependentOfCardEqFinrank hind hcard) = ![u, v, w] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hind hcard
  set bas := basisOfLinearIndependentOfCardEqFinrank hind hcard with hbasdef
  have hz : ∀ i, inner ℝ (y - y') (bas i) = (0 : ℝ) := by
    intro i
    fin_cases i <;> simp [hbas, inner_sub_left, h1, h2, h3]
  have key : inner ℝ (y - y') (y - y') = (0 : ℝ) := by
    nth_rewrite 2 [show y - y' = ∑ i, bas.repr (y - y') i • bas i from (bas.sum_repr _).symm]
    rw [inner_sum]
    simp [real_inner_smul_right, hz]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

/-- The angle between the two dual vectors `Q p - R q` and `P q - R p` is the supplement of
the angle between `p` and `q`. -/
