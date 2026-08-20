import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (hineq : covol * 2 ^ (Module.finrank ℝ E) < μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  have hineq' : μ F * 2 ^ (Module.finrank ℝ E) < μ s := by
    simpa [hμF] using hineq
  exact
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hineq'

/-- Covolume-shaped wrapper for the non-strict Minkowski inequality.

This is the “≤” analog of `minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt`.
-/
