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

theorem bell_theorem :
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (A B : Bool → Ω → ℝ),
        (∀ i, Measurable (A i)) ∧ (∀ j, Measurable (B j)) ∧
        (∀ i ω, |A i ω| ≤ 1) ∧ (∀ j ω, |B j ω| ≤ 1) ∧
        (∀ i j, lhvCorr μ (A i) (B j) = quantumCorr i j) := by
  rintro ⟨Ω, _, μ, hμ, A, B, hA, hB, bA, bB, hcorr⟩
  have key := chsh_classical μ (A false) (A true) (B false) (B true)
    (hA false) (hA true) (hB false) (hB true) (bA false) (bA true) (bB false) (bB true)
  rw [hcorr false false, hcorr false true, hcorr true false, hcorr true true,
    quantum_chsh_value] at key
  have h2 := two_sqrt_two_gt_two
  have : (2 : ℝ) * Real.sqrt 2 ≤ 2 := le_trans (le_abs_self _) key
  linarith

/-- The class of local hidden-variable models in `bell_theorem` is non-empty: for instance the
deterministic model with all outcomes equal to `+1`, which produces all correlations equal to `1`.
So `bell_theorem` is not vacuous. -/
