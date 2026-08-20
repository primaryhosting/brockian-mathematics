import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt
    {n : ℕ}
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) < volume s) :
    ∃ p : L, p ≠ 0 ∧ (p : (Fin n → ℝ)) ∈ s := by
  simpa using
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
      (E := (Fin n → ℝ)) (μ := volume) (L := L) (F := F) (s := s) hfund hsymm hconv hineq

/-- Minkowski (strict), returning the witness in `E` with membership proof in `L`.

This is often the most convenient output shape when downstream steps want to avoid subtype coercions.
-/
