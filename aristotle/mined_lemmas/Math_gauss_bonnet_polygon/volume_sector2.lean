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

lemma volume_sector2 (φ : ℝ) (h0 : 0 < φ) (h1 : φ < π) :
    volume (sector2 φ) = ENNReal.ofReal ((π - φ) / 2) := by
  have hS := measurableSet_sector2 φ
  have key : volume (sector2 φ) =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * (sector2 φ).indicator 1 (polarCoord.symm p) := by
    rw [← lintegral_indicator_one hS,
      ← lintegral_comp_polarCoord_symm (fun p => (sector2 φ).indicator 1 p)]
    simp [smul_eq_mul]
  set B : Set (ℝ × ℝ) := (Ioc (0 : ℝ) 1) ×ˢ (Icc (φ - π / 2) (π / 2)) with hB
  have hBmeas : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Icc
  have hBsub : B ⊆ polarCoord.target := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    simp only [mem_Icc] at ht
    exact ⟨hr.1, by constructor <;> [linarith [ht.1]; linarith [ht.2, Real.pi_pos]]⟩
  have hcongr : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 * (sector2 φ).indicator 1 (polarCoord.symm p)
        = B.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    simp only [mem_Ioi] at hr
    simp only [mem_Ioo] at ht
    have hpyth := Real.sin_sq_add_cos_sq t
    have hmem : (polarCoord.symm (r, t)) ∈ sector2 φ ↔ (r, t) ∈ B := by
      simp only [polarCoord_symm_apply, sector2, mem_setOf_eq, hB, mem_prod, mem_Ioc, mem_Icc]
      have hcc := cos_cond φ t h0 h1 ht.1 ht.2
      have e : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by nlinarith
      constructor
      · rintro ⟨hn, hc1, hc2⟩
        rw [e] at hn
        have hr2 : r ≤ 1 := by nlinarith
        have hcos : 0 ≤ Real.cos t := by nlinarith
        have hcos2 : 0 ≤ Real.cos (t - φ) := by rw [Real.cos_sub]; nlinarith
        exact ⟨⟨hr, hr2⟩, hcc.1 ⟨hcos, hcos2⟩⟩
      · rintro ⟨⟨-, hr2⟩, hts⟩
        obtain ⟨hcos, hcos2⟩ := hcc.2 hts
        rw [Real.cos_sub] at hcos2
        exact ⟨by rw [e]; nlinarith, by nlinarith, by nlinarith⟩
    by_cases hin : (r, t) ∈ B
    · rw [indicator_of_mem (hmem.2 hin), indicator_of_mem hin]; simp
    · rw [indicator_of_notMem (fun h => hin (hmem.1 h)), indicator_of_notMem hin]; simp
  rw [key, setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr,
    lintegral_indicator hBmeas, Measure.restrict_restrict hBmeas,
    inter_eq_self_of_subset_left hBsub, box_lint]
  congr 1
  ring

