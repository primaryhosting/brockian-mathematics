import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem cos_nonneg_pair_iff (θ φ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) (hφ : φ ∈ Ioo (-π) π) :
    (0 ≤ cos φ ∧ 0 ≤ cos θ * cos φ + sin θ * sin φ) ↔ φ ∈ Icc (θ - π / 2) (π / 2) := by
  have key : cos θ * cos φ + sin θ * sin φ = cos (φ - θ) := by rw [Real.cos_sub]; ring
  have hpi := Real.pi_pos
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    have hup : φ ≤ π / 2 := by
      by_contra h; push_neg at h
      exact absurd h1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hφ.2])))
    have hlo : -(π / 2) ≤ φ := by
      by_contra h; push_neg at h
      have : cos (-φ) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hφ.1])
      rw [Real.cos_neg] at this; linarith
    refine ⟨?_, hup⟩
    by_contra h
    push_neg at h
    have h3 : π / 2 < -(φ - θ) := by linarith
    have h4 : -(φ - θ) < π + π / 2 := by linarith
    have := Real.cos_neg_of_pi_div_two_lt_of_lt h3 h4
    rw [Real.cos_neg] at this; linarith
  · rintro ⟨h1, h2⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

