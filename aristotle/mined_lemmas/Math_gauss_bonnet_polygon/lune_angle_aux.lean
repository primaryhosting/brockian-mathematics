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

lemma lune_angle_aux (p q : E3) (P Q R D : ℝ)
    (hPdef : P = inner ℝ p p) (hQdef : Q = inner ℝ q q) (hRdef : R = inner ℝ p q)
    (hnp : ‖p‖ ^ 2 = P) (hnq : ‖q‖ ^ 2 = Q)
    (hPpos : 0 < P) (hQpos : 0 < Q) (hD : D = P * Q - R ^ 2) (hDpos : 0 < D)
    (hm0sq : ‖Q • p - R • q‖ ^ 2 = Q * D) :
    angle (D⁻¹ • (Q • p - R • q)) (D⁻¹ • (P • q - R • p)) = π - angle p q := by
  have hn0sq : ‖P • q - R • p‖ ^ 2 = P * D := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hnp, hnq, hD, real_inner_comm p q, ← hRdef]
    ring
  have hinner : inner ℝ (Q • p - R • q) (P • q - R • p) = -R * D := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm p q, ← hRdef, ← hPdef, ← hQdef, hD]
    ring
  have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
  have hqpos : 0 < ‖q‖ := by nlinarith [norm_nonneg q]
  have hnormprod : ‖Q • p - R • q‖ * ‖P • q - R • p‖ = D * (‖p‖ * ‖q‖) := by
    have h1 : (0 : ℝ) ≤ ‖Q • p - R • q‖ * ‖P • q - R • p‖ := by positivity
    have h2 : (0 : ℝ) ≤ D * (‖p‖ * ‖q‖) := by positivity
    have hsq : (‖Q • p - R • q‖ * ‖P • q - R • p‖) ^ 2 = (D * (‖p‖ * ‖q‖)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hm0sq, hn0sq, hnp, hnq]; ring
    calc ‖Q • p - R • q‖ * ‖P • q - R • p‖
        = √((‖Q • p - R • q‖ * ‖P • q - R • p‖) ^ 2) := (Real.sqrt_sq h1).symm
      _ = √((D * (‖p‖ * ‖q‖)) ^ 2) := by rw [hsq]
      _ = D * (‖p‖ * ‖q‖) := Real.sqrt_sq h2
  rw [angle_smul_left_of_pos _ _ (by positivity), angle_smul_right_of_pos _ _ (by positivity)]
  show Real.arccos _ = π - Real.arccos _
  rw [hinner, hnormprod, ← hRdef, ← Real.arccos_neg]
  congr 1
  field_simp

/-- **The lune at a vertex.**  For a nondegenerate spherical triangle `u v w`, there are
vectors `m`, `n` dual to `v` and `w` (in the basis `u, v, w`), and the angle between them is
the supplement of the interior angle of the triangle at `u`.  The corresponding lune is
`{x | 0 ≤ ⟪m, x⟫ ∧ 0 ≤ ⟪n, x⟫}`. -/
