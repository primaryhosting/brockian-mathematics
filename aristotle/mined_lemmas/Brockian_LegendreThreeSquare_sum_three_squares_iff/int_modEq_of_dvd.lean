import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma int_modEq_of_dvd {a b m M : ℤ} (h : a ≡ b [ZMOD M]) (hm : m ∣ M) : a ≡ b [ZMOD m] :=
  Int.ModEq.of_dvd hm h

end GeometryOfNumbers.NumberTheory


import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Countable
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import GeometryOfNumbers.Legendre.Exceptions
import GeometryOfNumbers.Legendre.AnkenyLemmas
import GeometryOfNumbers.Core.MinkowskiHelpers
import GeometryOfNumbers.Core.MinkowskiEngine
import GeometryOfNumbers.NumberTheory.Utils

-- This file is long and currently has a number of `simpa` calls that the linter considers
-- replaceable by `simp`. That warning is low-signal during active development, so we disable it
-- to keep `lake lint` output actionable.
set_option linter.unnecessarySimpa false

namespace GeometryOfNumbers
open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix
open scoped NumberTheorySymbols

/-! We work in `ℝ^3` as `Fin 3 → ℝ`, which matches Mathlib’s `volume` conventions. -/
abbrev E3 := (Fin 3 → ℝ)

/-!
## Ankeny’s ellipsoid (L2-ball presentation)

We keep the *ambient type* as `E3 := Fin 3 → ℝ` (matching `volume` conventions), but we want an L2-ball.
The clean trick is to define the ball as a preimage under `WithLp.toLp 2`, landing in
`EuclideanSpace ℝ (Fin 3)`.

This is the exact setup used in `Experiments/AnkenyL2Ellipsoid.lean`, but here we keep it in the main file
because it is load-bearing for Minkowski.
-/

abbrev E3L2 := EuclideanSpace ℝ (Fin 3)

