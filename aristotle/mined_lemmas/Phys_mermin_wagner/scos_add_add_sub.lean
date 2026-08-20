/-
Classical `XY`-type models with a continuous (rotation) symmetry, and the
Mermin–Wagner / Pfister "two–shift" bound on the magnetization in terms of the
Dirichlet energy of a cut-off function.
-/
import Mathlib

open MeasureTheory Real

noncomputable section

namespace MerminWagner

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`.  The continuous symmetry group of the
models below is the rotation group of this circle acting diagonally on all spins. -/
abbrev Spin : Type := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma scos_add_add_sub (z : Spin) (t : ℝ) :
    scos (z + (t : Spin)) + scos (z - (t : Spin)) = 2 * scos z * Real.cos t := by
  induction z using QuotientAddGroup.induction_on with
  | _ s =>
    have h1 : ((s : Spin) + (t : Spin)) = ((s + t : ℝ) : Spin) := by push_cast; ring
    have h2 : ((s : Spin) - (t : Spin)) = ((s - t : ℝ) : Spin) := by push_cast; ring
    rw [h1, h2, scos_coe, scos_coe, scos_coe, Real.cos_add, Real.cos_sub]
    ring

