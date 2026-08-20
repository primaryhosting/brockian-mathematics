/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem sector_angle_iff (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) (φ : ℝ) (hφ : φ ∈ Ioo (-π) π) :
    (0 < Real.cos φ ∧ 0 < Real.cos (φ - θ)) ↔ (θ - π/2 < φ ∧ φ < π/2) := by
  obtain ⟨h1, h2⟩ := hφ
  constructor
  · rintro ⟨hc1, hc2⟩
    have hlt : φ < π/2 := by
      by_contra h
      push_neg at h
      have : Real.cos φ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
      linarith
    have hgt : -(π/2) < φ := by
      by_contra h
      push_neg at h
      have : Real.cos φ ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
    refine ⟨?_, hlt⟩
    by_contra h
    push_neg at h
    have : Real.cos (φ - θ) ≤ 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith
  · rintro ⟨ha, hb⟩
    exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, hb⟩,
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩

