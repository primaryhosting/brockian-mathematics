import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd
    {E L : Type*} [MeasurableSpace E] (μ : Measure E) (F s : Set E)
    [AddGroup L] [Countable L] [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E]
    [MeasureTheory.VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ)
    (hS : MeasureTheory.NullMeasurableSet s μ)
    (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  simpa using MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd
    (μ := μ) (F := F) (s := s) fund hS h

/-- Covolume-shaped wrapper for Blichfeldt's theorem.

This is a rewrite helper, analogous to `minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt`.
It is useful when you have computed `μ F = covol` and want to state the hypothesis using `covol`
directly.
-/
