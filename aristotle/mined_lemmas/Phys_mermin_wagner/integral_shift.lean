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

lemma integral_shift (F : (V → Spin) → ℝ) (u : V → Spin) :
    ∫ θ, F (θ + u) ∂(refMeasure V) = ∫ θ, F θ ∂(refMeasure V) := by
  have := integral_add_left_eq_self (μ := refMeasure V) F u
  simpa [add_comm] using this

/-- The energy of a configuration: a (ferromagnetic) rotation invariant pair
interaction, together with arbitrary single–site terms `b`, which encode boundary
conditions and external fields (these are the symmetry-breaking terms). -/
