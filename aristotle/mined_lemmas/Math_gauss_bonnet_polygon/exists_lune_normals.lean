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

theorem exists_lune_normals (u v w : E3) (hu : ‖u‖ = 1) (hind : LinearIndependent ℝ ![u, v, w]) :
    (0 < sphericalAngle u v w ∧ sphericalAngle u v w < π) ∧
    ∃ m n : E3,
      (inner ℝ m u = (0 : ℝ) ∧ inner ℝ m v = (1 : ℝ) ∧ inner ℝ m w = (0 : ℝ)) ∧
      (inner ℝ n u = (0 : ℝ) ∧ inner ℝ n v = (0 : ℝ) ∧ inner ℝ n w = (1 : ℝ)) ∧
      angle m n = π - sphericalAngle u v w := by
  have huu : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  obtain ⟨p, hp⟩ : ∃ p : E3, p = v - (inner ℝ u v : ℝ) • u := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : E3, q = w - (inner ℝ u w : ℝ) • u := ⟨_, rfl⟩
  have hsa : sphericalAngle u v w = angle p q := by rw [sphericalAngle, hp, hq]
  have hv : v = p + (inner ℝ u v : ℝ) • u := by rw [hp]; abel
  have hw : w = q + (inner ℝ u w : ℝ) • u := by rw [hq]; abel
  have hpu : inner ℝ p u = (0 : ℝ) := by
    rw [hp, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
  have hqu : inner ℝ q u = (0 : ℝ) := by
    rw [hq, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = inner ℝ p p := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = inner ℝ q q := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = inner ℝ p q := ⟨_, rfl⟩
  have hpv : inner ℝ p v = P := by
    nth_rewrite 1 [hv]; rw [inner_add_right, real_inner_smul_right, hpu, hPdef]; ring
  have hpw : inner ℝ p w = R := by
    nth_rewrite 1 [hw]; rw [inner_add_right, real_inner_smul_right, hpu, hRdef]; ring
  have hqv : inner ℝ q v = R := by
    nth_rewrite 1 [hv]
    rw [inner_add_right, real_inner_smul_right, hqu, hRdef, real_inner_comm p q]; ring
  have hqw : inner ℝ q w = Q := by
    nth_rewrite 1 [hw]; rw [inner_add_right, real_inner_smul_right, hqu, hQdef]; ring
  have hnp : ‖p‖ ^ 2 = P := by rw [hPdef, real_inner_self_eq_norm_sq]
  have hnq : ‖q‖ ^ 2 = Q := by rw [hQdef, real_inner_self_eq_norm_sq]
  have hnotmul : ∀ r : ℝ, q ≠ r • p := by
    intro r hr
    have h2 : (r * (inner ℝ u v : ℝ) - (inner ℝ u w : ℝ)) • u + (-r) • v + (1 : ℝ) • w = 0 := by
      rw [show (r * (inner ℝ u v : ℝ) - (inner ℝ u w : ℝ)) • u + (-r) • v + (1 : ℝ) • w
        = (w - (inner ℝ u w : ℝ) • u) - r • (v - (inner ℝ u v : ℝ) • u) from by module,
        ← hp, ← hq, hr, sub_self]
    exact one_ne_zero (indep_coeffs hind h2).2.2
  have hPpos : 0 < P := by
    rw [hPdef, real_inner_self_pos]
    intro h0
    have h1 : v - (inner ℝ u v : ℝ) • u = 0 := by rw [← hp]; exact h0
    have h2 : (-(inner ℝ u v : ℝ)) • u + (1 : ℝ) • v + (0 : ℝ) • w = 0 := by
      rw [show (-(inner ℝ u v : ℝ)) • u + (1 : ℝ) • v + (0 : ℝ) • w
        = v - (inner ℝ u v : ℝ) • u from by module]
      exact h1
    exact one_ne_zero (indep_coeffs hind h2).2.1
  have hQpos : 0 < Q := by
    rw [hQdef, real_inner_self_pos]
    intro h0
    exact hnotmul 0 (by rw [h0, zero_smul])
  have hangle_pos : 0 < angle p q := by
    rcases eq_or_lt_of_le (angle_nonneg p q) with h | h
    · exact absurd (angle_eq_zero_iff.mp h.symm)
        (by rintro ⟨-, r, -, hr⟩; exact hnotmul r hr)
    · exact h
  have hangle_lt : angle p q < π := by
    rcases eq_or_lt_of_le (angle_le_pi p q) with h | h
    · exact absurd (angle_eq_pi_iff.mp h) (by rintro ⟨-, r, -, hr⟩; exact hnotmul r hr)
    · exact h
  have hm0sq : ‖Q • p - R • q‖ ^ 2 = Q * (P * Q - R ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hnp, hnq, ← hRdef]
    ring
  have hDpos : 0 < P * Q - R ^ 2 := by
    rcases lt_or_eq_of_le (by nlinarith [sq_nonneg ‖Q • p - R • q‖, norm_nonneg (Q • p - R • q)] :
        (0 : ℝ) ≤ P * Q - R ^ 2) with h | h
    · exact h
    · exfalso
      have hz : ‖Q • p - R • q‖ = 0 := by nlinarith [norm_nonneg (Q • p - R • q)]
      have hz2 : Q • p - R • q = 0 := norm_eq_zero.mp hz
      have h2 : (-(Q * (inner ℝ u v : ℝ)) + R * (inner ℝ u w : ℝ)) • u + Q • v + (-R) • w = 0 := by
        rw [← hz2, hp, hq]; module
      exact absurd (indep_coeffs hind h2).2.1 hQpos.ne'
  have hne : P * Q - R ^ 2 ≠ 0 := hDpos.ne'
  refine ⟨⟨hsa ▸ hangle_pos, hsa ▸ hangle_lt⟩,
    (P * Q - R ^ 2)⁻¹ • (Q • p - R • q), (P * Q - R ^ 2)⁻¹ • (P • q - R • p),
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [real_inner_smul_left, inner_sub_left, hpu, hqu]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpv, hqv]; field_simp
  · simp only [real_inner_smul_left, inner_sub_left, hpw, hqw]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpu, hqu]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpv, hqv]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpw, hqw]; field_simp
  rw [hsa]
  exact lune_angle_aux p q P Q R (P * Q - R ^ 2) hPdef hQdef hRdef hnp hnq hPpos hQpos rfl
    hDpos hm0sq

/-! ### Step 5: the eight sectors -/

/-- The sign of a boolean, as a real number. -/
