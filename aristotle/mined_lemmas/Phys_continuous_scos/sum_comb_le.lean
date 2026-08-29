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

lemma sum_comb_le {α : Type} {s : Finset α} (F₁ F₂ F₃ G : α → ℝ)
    (h : ∀ a ∈ s, F₁ a + F₂ a - 2 * F₃ a ≤ G a) :
    (∑ a ∈ s, F₁ a) + (∑ a ∈ s, F₂ a) - 2 * (∑ a ∈ s, F₃ a) ≤ ∑ a ∈ s, G a := by
  have hEq : (∑ a ∈ s, F₁ a) + (∑ a ∈ s, F₂ a) - 2 * (∑ a ∈ s, F₃ a)
      = ∑ a ∈ s, (F₁ a + F₂ a - 2 * F₃ a) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hEq]
  exact Finset.sum_le_sum h

/-- The energy cost of a spin wave is at most its Dirichlet energy. -/
