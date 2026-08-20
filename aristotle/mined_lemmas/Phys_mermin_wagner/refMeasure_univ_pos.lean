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

lemma refMeasure_univ_pos : 0 < (refMeasure V) Set.univ := by
  unfold refMeasure
  rw [Measure.pi_univ]
  simp [AddCircle.measure_univ]
  positivity

