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

private theorem integrable_prod {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hA1 : ∀ ω, |A ω| ≤ 1) (hB1 : ∀ ω, |B ω| ≤ 1) :
    Integrable (fun ω => A ω * B ω) μ := by
  refine ⟨(hA.mul hB).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards with ω
  have := abs_mul (A ω) (B ω)
  have h1 : |A ω| ≤ 1 := hA1 ω
  have h2 : |B ω| ≤ 1 := hB1 ω
  have h0 : (0:ℝ) ≤ |A ω| := abs_nonneg _
  simp only [Real.norm_eq_abs, this]
  nlinarith

/-- **The CHSH inequality for local hidden-variable models.**
If `A₁, A₂` (Alice) and `B₁, B₂` (Bob) are measurable `[-1,1]`-valued response functions of a
hidden variable distributed according to a probability measure `μ`, then the CHSH combination
of the resulting correlations is bounded by `2` in absolute value. -/
