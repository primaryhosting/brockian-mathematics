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

lemma snorm_le_snorm_add_unit (x : Site d) (i : Fin d) :
    snorm x ≤ snorm (x + unitVec i) + 1 := by
  classical
  refine Finset.sup_le ?_
  intro j _
  have h1 : (x + unitVec i) j = x j + (if j = i then 1 else 0) := by
    simp [unitVec, Pi.single_apply, eq_comm]
  have h2 : ((x + unitVec i) j).natAbs ≤ snorm (x + unitVec i) :=
    Finset.le_sup (f := fun j => ((x + unitVec i) j).natAbs) (Finset.mem_univ j)
  by_cases hj : j = i
  · have h1' : (x + unitVec i) j = x j + 1 := by rw [h1]; simp [hj]
    rw [h1'] at h2
    omega
  · have h1' : (x + unitVec i) j = x j := by rw [h1]; simp [hj]
    rw [h1'] at h2
    omega

