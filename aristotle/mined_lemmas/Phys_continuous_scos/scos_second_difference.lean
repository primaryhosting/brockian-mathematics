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

lemma scos_second_difference (a : Spin) (t : ℝ) :
    2 * scos a - scos (a + (t : Spin)) - scos (a - (t : Spin)) = 2 * scos a * (1 - Real.cos t) := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
    rw [← AddCircle.coe_add, ← AddCircle.coe_sub]
    simp only [scos_coe, Real.cos_add, Real.cos_sub]
    ring

/-- `1 - cos t ≤ t ^ 2 / 2`. -/
