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

lemma cos_cond (φ t : ℝ) (h0 : 0 < φ) (h1 : φ < π) (ht1 : -π < t) (ht2 : t < π) :
    (0 ≤ Real.cos t ∧ 0 ≤ Real.cos (t - φ)) ↔ (φ - π / 2 ≤ t ∧ t ≤ π / 2) := by
  constructor
  · rintro ⟨hc1, hc2⟩
    have hA : t ≤ π / 2 := by
      by_contra h
      push_neg at h
      have := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])
      linarith
    have hB : -(π / 2) ≤ t := by
      by_contra h
      push_neg at h
      have : Real.cos (-t) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
      rw [Real.cos_neg] at this; linarith
    refine ⟨?_, hA⟩
    by_contra h
    push_neg at h
    have : Real.cos (-(t - φ)) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rw [Real.cos_neg] at this; linarith
  · rintro ⟨hA, hB⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hB⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

