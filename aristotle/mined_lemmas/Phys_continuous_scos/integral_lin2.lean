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

lemma integral_lin2 {f₁ f₂ : (ι → Spin) → ℝ}
    (h₁ : Integrable f₁ (volume : Measure (ι → Spin)))
    (h₂ : Integrable f₂ (volume : Measure (ι → Spin))) (a b : ℝ) :
    ∫ θ, (a * f₁ θ + b * f₂ θ) = a * (∫ θ, f₁ θ) + b * (∫ θ, f₂ θ) := by
  rw [integral_add (h₁.const_mul a) (h₂.const_mul b), integral_const_mul, integral_const_mul]

