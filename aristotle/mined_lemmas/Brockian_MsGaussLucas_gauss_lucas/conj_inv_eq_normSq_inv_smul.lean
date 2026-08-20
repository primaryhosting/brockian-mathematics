import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

private lemma conj_inv_eq_normSq_inv_smul (u : ℂ) :
    (starRingEnd ℂ) u⁻¹ = ((Complex.normSq u)⁻¹ : ℝ) • u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have h : (starRingEnd ℂ) u * u = ((Complex.normSq u : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    have hcu : (starRingEnd ℂ) u ≠ 0 := by simpa using hu
    have hn : ((Complex.normSq u : ℝ) : ℂ) ≠ 0 := by
      rw [← h]; exact mul_ne_zero hcu hu
    rw [map_inv₀, Complex.real_smul, Complex.ofReal_inv]
    field_simp
    linear_combination -h

/-- Conjugating the relation `∑ (z - r i)⁻¹ = 0` gives a vanishing positively weighted sum. -/
