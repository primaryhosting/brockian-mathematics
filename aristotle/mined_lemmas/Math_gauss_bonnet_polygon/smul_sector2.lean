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

lemma smul_sector2 (φ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    r • sector2 φ =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.1 ∧
        0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · ext p
    simp only [zero_smul_set (⟨(0, 0), by simp [sector2]⟩ : (sector2 φ).Nonempty), mem_setOf_eq]
    constructor
    · rintro rfl; norm_num
    · rintro ⟨h1, h2, h3⟩
      have : p.1 = 0 ∧ p.2 = 0 := by constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      exact Prod.ext this.1 this.2
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hq
      refine ⟨by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; nlinarith, ?_, ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul]; positivity
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨r⁻¹ • p, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [mul_pow, mul_pow, ← mul_add]
        have h4 : (r⁻¹) ^ 2 * r ^ 2 = 1 := by field_simp
        nlinarith [sq_nonneg (r⁻¹), mul_le_mul_of_nonneg_left h1 (sq_nonneg r⁻¹)]
      · simp only [Prod.smul_fst, smul_eq_mul]; positivity
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have h5 : Real.cos φ * (r⁻¹ * p.1) + Real.sin φ * (r⁻¹ * p.2)
            = r⁻¹ * (Real.cos φ * p.1 + Real.sin φ * p.2) := by ring
        rw [h5]; positivity
      · simp [smul_smul, mul_inv_cancel₀ hr'.ne']

/-! ### Step 2: the volume of a spherical wedge, in coordinates -/

/-- The wedge of the unit ball of `ℝ × (ℝ × ℝ)` cut out by the two half-spaces
`0 ≤ y` and `0 ≤ y cos φ + z sin φ`.  Its dihedral angle is `π - φ`. -/
