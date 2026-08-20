import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (hineq : covol * 2 ^ (Module.finrank ℝ E) ≤ μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  have hineq' : μ F * 2 ^ (Module.finrank ℝ E) ≤ μ s := by
    simpa [hμF] using hineq
  exact
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq'

end GeometryOfNumbers


import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Minkowski / ellipsoid helpers (shared)

This file is the shared **definition layer** for the “diagonal map / ellipsoid as preimage of a
ball” normalization used in geometry-of-numbers arguments.

We intentionally keep this file *light* (definitions only). Proof-heavy facts (volume computations,
Minkowski inequalities, etc.) are developed in proof-specific files (e.g. Ankeny or experiments).
-/

noncomputable section

namespace GeometryOfNumbers.Minkowski

abbrev E3 := Fin 3 → ℝ

/-!
## Ankeny ellipsoid normalization

For Ankeny’s quadratic form

$$
Q(x,y,z) = 2q x^2 + y^2 + n z^2,
$$

the ellipsoid `Q(x) < (2*sqrt(n*q))^2` is the preimage of `ball 0 (2*sqrt(n*q))` under the diagonal
map `diag( sqrt(2q), 1, sqrt(n) )`.
-/

