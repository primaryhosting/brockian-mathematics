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

def magnetization (β : ℝ) (J : V → V → ℝ) (b : V → Spin → ℝ) (x₀ : V) (φ : Spin) : ℝ :=
    gibbsAvg β J b (fun θ => scos (θ x₀ - φ))

/-- The Dirichlet energy of a function `f` with respect to the couplings `J`. -/
