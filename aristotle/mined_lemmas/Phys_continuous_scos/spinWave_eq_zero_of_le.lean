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

lemma spinWave_eq_zero_of_le {R : ℕ} (hR : 1 ≤ R) {x : Site d} (hx : R ≤ snorm x) :
    spinWave R x = 0 := by
  have hlogpos : 0 < Real.log (1 + (R : ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hmono : Real.log (1 + (R : ℝ)) ≤ Real.log (1 + (snorm x : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have : (R:ℝ) ≤ (snorm x : ℝ) := by exact_mod_cast hx
    linarith
  have h1 : 1 ≤ Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)) :=
    (one_le_div hlogpos).2 hmono
  simp only [spinWave, max_eq_left_iff]
  linarith

/-! ### The energy estimate in dimension `d ≤ 2` -/

/-- An elementary logarithm step estimate: `log (1+b) - log (1+a) ≤ 1/(1+a)` for `b ≤ a+1`. -/
