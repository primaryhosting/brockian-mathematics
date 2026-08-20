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

theorem chsh_classical (A1 A2 B1 B2 : Ω → ℝ)
    (hA1 : Measurable A1) (hA2 : Measurable A2) (hB1 : Measurable B1) (hB2 : Measurable B2)
    (bA1 : ∀ ω, |A1 ω| ≤ 1) (bA2 : ∀ ω, |A2 ω| ≤ 1)
    (bB1 : ∀ ω, |B1 ω| ≤ 1) (bB2 : ∀ ω, |B2 ω| ≤ 1) :
    |lhvCorr μ A1 B1 + lhvCorr μ A1 B2 + lhvCorr μ A2 B1 - lhvCorr μ A2 B2| ≤ 2 := by
  have i11 := integrable_prod μ hA1 hB1 bA1 bB1
  have i12 := integrable_prod μ hA1 hB2 bA1 bB2
  have i21 := integrable_prod μ hA2 hB1 bA2 bB1
  have i22 := integrable_prod μ hA2 hB2 bA2 bB2
  have s1 : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω) μ := i11.add i12
  have s2 : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω) μ := s1.add i21
  have hint : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) μ :=
    s2.sub i22
  have hsplit : ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ
      = lhvCorr μ A1 B1 + lhvCorr μ A1 B2 + lhvCorr μ A2 B1 - lhvCorr μ A2 B2 := by
    rw [integral_sub s2 i22, integral_add s1 i21, integral_add i11 i12]
    rfl
  have hbd : ∀ ω, |A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω| ≤ 2 := fun ω =>
    chsh_pointwise _ _ _ _ (bA1 ω) (bA2 ω) (bB1 ω) (bB2 ω)
  have hup : ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ ≤ 2 := by
    have := integral_mono hint (integrable_const (2:ℝ))
      (fun ω => (abs_le.mp (hbd ω)).2)
    simpa using this
  have hlow : -2 ≤ ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ := by
    have := integral_mono (integrable_const (-2:ℝ)) hint
      (fun ω => (abs_le.mp (hbd ω)).1)
    simpa using this
  rw [← hsplit, abs_le]
  exact ⟨hlow, hup⟩

end LHV

/-- Alice's two measurement angles. -/
