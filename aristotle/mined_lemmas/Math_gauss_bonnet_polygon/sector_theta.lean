import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma sector_theta (psi theta : ℝ) (h0 : 0 < psi) (hpi : psi < π) (hθ : theta ∈ Ioo (-π) π) :
    (0 ≤ cos theta ∧ 0 ≤ cos psi * cos theta + sin psi * sin theta)
      ↔ theta ∈ Icc (psi - π / 2) (π / 2) := by
  have hcs : cos psi * cos theta + sin psi * sin theta = cos (theta - psi) := by
    rw [Real.cos_sub]; ring
  rw [hcs]
  obtain ⟨hθ1, hθ2⟩ := hθ
  constructor
  · rintro ⟨hc1, hc2⟩
    have hup : theta ≤ π / 2 := by
      by_contra hcon
      push_neg at hcon
      exact absurd hc1 (not_le.mpr
        (Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith [Real.pi_pos])))
    have hlow : -(π / 2) ≤ theta := by
      by_contra hcon
      push_neg at hcon
      have : cos theta < 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
      linarith
    refine ⟨?_, hup⟩
    by_contra hcon
    push_neg at hcon
    have : cos (theta - psi) < 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    linarith
  · rintro ⟨hl, hu⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hu⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

/-- An integral over a product set of a function of the first variable. -/
