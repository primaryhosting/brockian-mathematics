/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real

namespace Frontier

/-- **Pointwise CHSH bound.** For real numbers of absolute value at most `1`,
the CHSH combination `a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂` has absolute value at most `2`. -/

theorem chsh_pointwise (a1 a2 b1 b2 : ℝ) (h1 : |a1| ≤ 1) (h2 : |a2| ≤ 1)
    (h3 : |b1| ≤ 1) (h4 : |b2| ≤ 1) :
    |a1 * b1 + a1 * b2 + a2 * b1 - a2 * b2| ≤ 2 := by
  rw [abs_le] at *
  obtain ⟨p1, q1⟩ := h1; obtain ⟨p2, q2⟩ := h2; obtain ⟨p3, q3⟩ := h3; obtain ⟨p4, q4⟩ := h4
  constructor <;>
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 + b2)]

section LHV

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The correlation predicted by a local hidden-variable model with hidden-variable
distribution `μ` and local response functions `A i`, `B j`. -/
