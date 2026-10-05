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

lemma extend_sub_shift (N : ℕ) (τ : Site d → Spin) (f : Site d → ℝ)
    (hsupp : ∀ x, x ∉ box d N → f x = 0) (θ : BoxCfg d N) (x : Site d) :
    extend N τ (θ - shiftOf N f) x = extend N τ θ x - ((f x : ℝ) : Spin) := by
  unfold extend shiftOf
  by_cases h : x ∈ box d N
  · simp [h]
  · simp [h, hsupp x h]

