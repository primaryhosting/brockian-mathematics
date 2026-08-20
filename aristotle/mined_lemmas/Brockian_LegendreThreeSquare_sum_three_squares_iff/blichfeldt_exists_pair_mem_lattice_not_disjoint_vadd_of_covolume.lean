import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd_of_covolume
    {E L : Type*} [MeasurableSpace E] (μ : Measure E) (F s : Set E)
    [AddGroup L] [Countable L] [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E]
    [MeasureTheory.VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ)
    (hS : MeasureTheory.NullMeasurableSet s μ)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (h : covol < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  have h' : μ F < μ s := by simpa [hμF] using h
  exact blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd (μ := μ) (F := F) (s := s) fund hS h'

/-- A thin wrapper around Mathlib's Minkowski theorem.

This is intentionally small: the “engine” is Mathlib; our value-add is a stable local interface.
-/
