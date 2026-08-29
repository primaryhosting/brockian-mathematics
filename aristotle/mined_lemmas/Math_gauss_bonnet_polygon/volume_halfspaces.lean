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

lemma volume_halfspaces (a b : E3) (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : 0 < angle a b) (h1 : angle a b < π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ inner ℝ a x ∧ 0 ≤ inner ℝ b x}
      = ENNReal.ofReal (2 * (π - angle a b) / 3) := by
  obtain ⟨e1, e2, hne1, hne2, h12, hadec, hbdec⟩ := exists_frame a b ha hb h0 h1
  obtain ⟨B, hB0, hB1⟩ := exists_onb e1 e2 hne1 hne2 h12
  have hA : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hBn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hFmp : MeasurePreserving (fun x : E3 => coordEquiv (WithLp.ofLp (B.repr x)))
      volume volume :=
    measurePreserving_coordEquiv.comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).comp B.measurePreserving_repr)
  have hset : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ inner ℝ a x ∧ 0 ≤ inner ℝ b x}
      = (fun x : E3 => coordEquiv (WithLp.ofLp (B.repr x))) ⁻¹' wedge3 (angle a b) := by
    ext x
    have hxi : ∀ i, (WithLp.ofLp (B.repr x)) i = inner ℝ (B i) x := fun i =>
      B.repr_apply_apply x i
    have hnorm : ‖x‖ = √ ((inner ℝ (B 0) x) ^ 2 + (inner ℝ (B 1) x) ^ 2
        + (inner ℝ (B 2) x) ^ 2) := by
      rw [← B.repr.norm_map x, EuclideanSpace.norm_eq]
      congr 1
      rw [Fin.sum_univ_three]
      simp [hxi, Real.norm_eq_abs, sq_abs]
    have hax : inner ℝ a x = ‖a‖ * inner ℝ (B 0) x := by
      rw [hB0]; nth_rewrite 1 [hadec]; rw [real_inner_smul_left]
    have hbx : inner ℝ b x = ‖b‖ * (Real.cos (angle a b) * inner ℝ (B 0) x
        + Real.sin (angle a b) * inner ℝ (B 1) x) := by
      rw [hB0, hB1]; nth_rewrite 1 [hbdec]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    simp only [mem_setOf_eq, mem_preimage, wedge3, coordEquiv_apply, hxi]
    rw [hnorm, hax, hbx, Real.sqrt_le_one]
    constructor
    · rintro ⟨hn, hp, hq⟩
      exact ⟨by linarith, by nlinarith, by nlinarith⟩
    · rintro ⟨hn, hp, hq⟩
      exact ⟨by linarith, by nlinarith, by nlinarith⟩
  rw [hset, hFmp.measure_preimage (isClosed_wedge3 _).measurableSet.nullMeasurableSet,
    volume_wedge3 _ h0 h1]

end GaussBonnet

