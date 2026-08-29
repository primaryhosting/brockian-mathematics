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

def spinWave (R : ℕ) (x : Site d) : ℝ :=
  max 0 (1 - Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)))

/-- The Dirichlet energy of the spin wave, computed over all bonds of the box of
radius `N + 1`. -/
