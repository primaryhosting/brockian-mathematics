import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (hineq : μ F * 2 ^ (Module.finrank ℝ E) ≤ μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  simpa using
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq

/-- Minkowski (non-strict) with `volume` as the ambient Haar measure. -/
