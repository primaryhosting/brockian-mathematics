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

lemma log_step_bound (a b : ℕ) (hb : b ≤ a + 1) :
    Real.log (1 + (b:ℝ)) - Real.log (1 + (a:ℝ)) ≤ 1 / (1 + (a:ℝ)) := by
  have hpos : (0:ℝ) < 1 + (a:ℝ) := by positivity
  have hbpos : (0:ℝ) < 1 + (b:ℝ) := by positivity
  have hlog : Real.log (1 + (b:ℝ)) - Real.log (1 + (a:ℝ))
      = Real.log ((1 + (b:ℝ)) / (1 + (a:ℝ))) := (Real.log_div (ne_of_gt hbpos) (ne_of_gt hpos)).symm
  rw [hlog]
  have h2 := Real.log_le_sub_one_of_pos (x := (1 + (b:ℝ)) / (1 + (a:ℝ))) (by positivity)
  have hb' : (b:ℝ) ≤ (a:ℝ) + 1 := by exact_mod_cast hb
  have h3 : (1 + (b:ℝ)) / (1 + (a:ℝ)) - 1 ≤ 1 / (1 + (a:ℝ)) := by
    rw [← sub_nonpos]
    have heq : (1 + (b:ℝ)) / (1 + (a:ℝ)) - 1 - 1 / (1 + (a:ℝ))
        = ((b:ℝ) - (a:ℝ) - 1) / (1 + (a:ℝ)) := by field_simp; ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
  linarith

/-- Gradient bound for the logarithmic profile. -/
