import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma integral_lin3 {f₁ f₂ f₃ : (ι → Spin) → ℝ}
    (h₁ : Integrable f₁ (volume : Measure (ι → Spin)))
    (h₂ : Integrable f₂ (volume : Measure (ι → Spin)))
    (h₃ : Integrable f₃ (volume : Measure (ι → Spin))) (a b c : ℝ) :
    ∫ θ, (a * f₁ θ + b * f₂ θ + c * f₃ θ)
      = a * (∫ θ, f₁ θ) + b * (∫ θ, f₂ θ) + c * (∫ θ, f₃ θ) := by
  have h : ∫ θ, ((1:ℝ) * (a * f₁ θ + b * f₂ θ) + c * f₃ θ)
      = 1 * (∫ θ, (a * f₁ θ + b * f₂ θ)) + c * (∫ θ, f₃ θ) :=
    integral_lin2 ((h₁.const_mul a).add (h₂.const_mul b)) h₃ 1 c
  simp only [one_mul] at h
  rw [h, integral_lin2 h₁ h₂ a b]

/-- **Spin-wave estimate.**  If the second difference of the Hamiltonian along the
deformation `g` is bounded by `K`, then shifting a bounded observable by `g` changes its
Gibbs expectation by at most `C √(2βK)`. -/
