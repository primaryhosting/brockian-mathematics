import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

private lemma sum_normSq_inv_smul_eq_zero {n : ℕ} (r : Fin n → ℂ) (z : ℂ)
    (hsum : ∑ i, (z - r i)⁻¹ = 0) :
    ∑ i, ((Complex.normSq (z - r i))⁻¹ : ℝ) • (z - r i) = 0 := by
  have h := congrArg (starRingEnd ℂ) hsum
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => (conj_inv_eq_normSq_inv_smul (z - r i)).symm

/-- If `z` is different from all of the points `r i` and the sum of `(z - r i)⁻¹` vanishes,
then `z` lies in the convex hull of the `r i`. -/
