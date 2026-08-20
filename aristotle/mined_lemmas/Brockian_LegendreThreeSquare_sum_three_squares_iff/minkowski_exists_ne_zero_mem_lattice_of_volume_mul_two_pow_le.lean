import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_le
    {n : ℕ}
    [Nontrivial (Fin n → ℝ)]
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) ≤ volume s) :
    ∃ p : L, p ≠ 0 ∧ (p : (Fin n → ℝ)) ∈ s := by
  simpa using
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
      (E := (Fin n → ℝ)) (μ := volume) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq

/-- Covolume-shaped wrapper for the strict Minkowski inequality.

This is just a rewrite helper: if you have already computed `μ F = covol` (e.g. from an explicit
fundamental domain volume computation), you can state the Minkowski inequality using `covol`
directly.
-/
