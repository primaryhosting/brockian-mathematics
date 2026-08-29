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

lemma volume_wedge3 (φ : ℝ) (h0 : 0 < φ) (h1 : φ < π) :
    volume (wedge3 φ) = ENNReal.ofReal (2 * (π - φ) / 3) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (isClosed_wedge3 φ).measurableSet]
  have hslice : ∀ z : ℝ, volume (Prod.mk z ⁻¹' wedge3 φ)
      = ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal ((π - φ) / 2) := by
    intro z
    rcases le_or_gt (z ^ 2) 1 with hz | hz
    · have hr : (0 : ℝ) ≤ √(1 - z ^ 2) := Real.sqrt_nonneg _
      have hr2 : (√(1 - z ^ 2)) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
      have hset : Prod.mk z ⁻¹' wedge3 φ = (√(1 - z ^ 2)) • sector2 φ := by
        rw [smul_sector2 φ hr, hr2]
        ext p
        simp only [wedge3, mem_preimage, mem_setOf_eq]
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨by linarith, b, c⟩
        · rintro ⟨a, b, c⟩; exact ⟨by linarith, b, c⟩
      rw [hset, Measure.addHaar_smul, volume_sector2 φ h0 h1]
      congr 2
      have h6 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
      rw [h6, hr2, abs_of_nonneg (by linarith)]
    · have h7 : Prod.mk z ⁻¹' wedge3 φ = ∅ := by
        ext p
        simp only [wedge3, mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨a, b, c⟩
        nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      rw [h7, measure_empty, ENNReal.ofReal_eq_zero.2 (by linarith), zero_mul]
  simp_rw [hslice]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hint : ∫⁻ z : ℝ, ENNReal.ofReal (1 - z ^ 2) = ENNReal.ofReal (4 / 3) := by
    have hsupp : (fun z : ℝ => ENNReal.ofReal (1 - z ^ 2))
        = (Icc (-1 : ℝ) 1).indicator (fun z => ENNReal.ofReal (1 - z ^ 2)) := by
      ext z
      by_cases hz : z ∈ Icc (-1 : ℝ) 1
      · simp [hz]
      · rw [indicator_of_notMem hz, ENNReal.ofReal_eq_zero]
        simp only [mem_Icc, not_and_or, not_le] at hz
        rcases hz with h | h <;> nlinarith
    rw [hsupp, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
          ((continuous_pow 2).intervalIntegrable _ _)]
      norm_num
    · exact (Continuous.integrableOn_Icc (by fun_prop))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      simp only [mem_Icc, Pi.zero_apply] at hz ⊢; nlinarith [hz.1, hz.2]
  rw [hint, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-! ### Step 3: the volume of an intersection of two half-spaces with the unit ball -/

/-- The measurable identification of `ℝ³` with `ℝ × (ℝ × ℝ)` used to apply `volume_wedge3`. -/
