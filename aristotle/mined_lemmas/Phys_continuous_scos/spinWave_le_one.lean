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

lemma spinWave_le_one (R : ℕ) (x : Site d) : spinWave R x ≤ 1 := by
  unfold spinWave
  refine max_le (by norm_num) ?_
  have h1 : (0:ℝ) ≤ Real.log (1 + (snorm x : ℝ)) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (snorm x : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (0:ℝ) ≤ Real.log (1 + (R : ℝ)) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    linarith
  have : 0 ≤ Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)) := div_nonneg h1 h2
  linarith

