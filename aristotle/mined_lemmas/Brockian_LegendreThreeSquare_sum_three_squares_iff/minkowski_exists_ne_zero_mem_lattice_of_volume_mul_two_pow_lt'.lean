import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt'
    {n : ℕ}
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) < volume s) :
    ∃ x : (Fin n → ℝ), x ≠ 0 ∧ x ∈ L ∧ x ∈ s := by
  rcases
      minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt
        (L := L) (F := F) (s := s) hfund hsymm hconv hineq with
    ⟨p, hp0, hp_mem⟩
  refine ⟨(p : (Fin n → ℝ)), ?_, ?_, hp_mem⟩
  · -- `p ≠ 0` in the subtype implies the coerced element is not `0`.
    intro h
    apply hp0
    apply Subtype.ext
    simpa using h
  · exact p.property

/-- A thin wrapper around Mathlib's “≤” Minkowski theorem.

Compared to `minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt`, this version requires
`s` to be compact and the lattice `L` to have the discrete topology, but it only assumes a weak
inequality.
-/
