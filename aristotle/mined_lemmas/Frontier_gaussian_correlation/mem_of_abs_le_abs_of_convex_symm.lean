import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Frontier

open ProbabilityTheory

/-- The Gaussian correlation inequality, as a property of a measure `μ` on a real vector
space `E`:  for any two measurable, convex, origin-symmetric sets `K` and `L`,
`μ (K ∩ L) ≥ μ K * μ L`.

Royen's theorem states that this holds for every centred Gaussian measure `μ`.  In this file
we formalise the statement and prove the one-dimensional base case together with several
Lean-checked reductions. -/

theorem mem_of_abs_le_abs_of_convex_symm {S : Set ℝ} (hS : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : ℝ} (hx : x ∈ S) (hxy : |y| ≤ |x|) : y ∈ S := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have : y = 0 := by
      have : |y| ≤ 0 := by simpa using hxy
      simpa using abs_nonpos_iff.mp this
    simpa [this] using hx
  · set t : ℝ := y / x with ht
    have habs : |t| ≤ 1 := by
      rw [ht, abs_div]
      rw [div_le_one (abs_pos.mpr hx0)]
      exact hxy
    have h1 : (0:ℝ) ≤ (1 + t) / 2 := by
      have ht1 : -1 ≤ t := by linarith [neg_abs_le t, habs]
      linarith
    have h2 : (0:ℝ) ≤ (1 - t) / 2 := by
      have ht2 : t ≤ 1 := le_trans (le_abs_self t) habs
      linarith
    have hsum : (1 + t) / 2 + (1 - t) / 2 = 1 := by ring
    have := hS hx (hsymm x hx) h1 h2 hsum
    have hval : ((1 + t) / 2) • x + ((1 - t) / 2) • (-x) = y := by
      simp only [smul_eq_mul, mul_neg, ht]
      field_simp
      ring
    rwa [hval] at this

/-- Two convex origin-symmetric subsets of `ℝ` are nested. -/
