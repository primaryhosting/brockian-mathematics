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

lemma mem_box_iff {N : ℕ} {x : Site d} : x ∈ box d N ↔ snorm x ≤ N := by
  classical
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, snorm, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    have := h i
    omega

