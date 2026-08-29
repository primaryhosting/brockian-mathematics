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

lemma continuous_xyHam (N : ℕ) (τ : Site d → Spin) : Continuous (xyHam N τ) := by
  unfold xyHam
  refine continuous_finset_sum _ (fun x _ => continuous_finset_sum _ (fun i _ => ?_))
  exact continuous_const.sub
    (continuous_scos.comp ((continuous_extend_apply N τ x).sub (continuous_extend_apply N τ _)))

