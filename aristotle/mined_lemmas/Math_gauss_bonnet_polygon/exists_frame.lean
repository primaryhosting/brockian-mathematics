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

lemma exists_frame (a b : E3) (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : 0 < angle a b) (h1 : angle a b < π) :
    ∃ e1 e2 : E3, ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ inner ℝ e1 e2 = (0 : ℝ) ∧
      a = ‖a‖ • e1 ∧
      b = (‖b‖ * Real.cos (angle a b)) • e1 + (‖b‖ * Real.sin (angle a b)) • e2 := by
  have hA : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hBn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hsinpos : 0 < Real.sin (angle a b) := Real.sin_pos_of_pos_of_lt_pi h0 h1
  obtain ⟨e1, he1⟩ : ∃ e1 : E3, e1 = ‖a‖⁻¹ • a := ⟨_, rfl⟩
  have hne1 : ‖e1‖ = 1 := by rw [he1, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hA.ne']
  have hadec : a = ‖a‖ • e1 := by rw [he1, smul_smul, mul_inv_cancel₀ hA.ne', one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = inner ℝ e1 b := ⟨_, rfl⟩
  have hcval : c = ‖b‖ * Real.cos (angle a b) := by
    rw [hc, he1, real_inner_smul_left, cos_angle]; field_simp
  obtain ⟨b', hb'⟩ : ∃ b' : E3, b' = b - c • e1 := ⟨_, rfl⟩
  have hperp : inner ℝ e1 b' = (0 : ℝ) := by
    rw [hb', inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hne1, ← hc]; ring
  have hcb : inner ℝ b e1 = c := by rw [hc, real_inner_comm]
  have hnb' : ‖b'‖ = ‖b‖ * Real.sin (angle a b) := by
    have hsq : ‖b'‖ ^ 2 = (‖b‖ * Real.sin (angle a b)) ^ 2 := by
      rw [hb', norm_sub_sq_real, real_inner_smul_right, hcb, norm_smul, hne1]
      simp only [Real.norm_eq_abs, mul_one]
      rw [sq_abs, hcval]
      linear_combination (-(‖b‖ ^ 2)) * (Real.sin_sq_add_cos_sq (angle a b))
    nlinarith [norm_nonneg b', mul_pos hBn hsinpos]
  have hnb'pos : 0 < ‖b'‖ := by rw [hnb']; positivity
  obtain ⟨e2, he2⟩ : ∃ e2 : E3, e2 = ‖b'‖⁻¹ • b' := ⟨_, rfl⟩
  have hne2 : ‖e2‖ = 1 := by
    rw [he2, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnb'pos.ne']
  have h12 : inner ℝ e1 e2 = (0 : ℝ) := by rw [he2, real_inner_smul_right, hperp, mul_zero]
  refine ⟨e1, e2, hne1, hne2, h12, hadec, ?_⟩
  have hb'e2 : ‖b'‖ • e2 = b' := by
    rw [he2, smul_smul, mul_inv_cancel₀ hnb'pos.ne', one_smul]
  rw [← hcval, ← hnb', hb'e2, hb']
  abel

/-- **Volume of a spherical wedge.**  For two nonzero vectors `a`, `b` of `ℝ³` spanning a plane,
the part of the unit ball on the positive side of both `a` and `b` has volume
`2(π - angle a b)/3`; equivalently the corresponding lune on the unit sphere has area
`2(π - angle a b)`. -/
