import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part n
  have hm_mod : m % 8 = 3 := squarefree_part_mod_eight n s m hm_eq hn
  have hm_odd : Odd m := by
    have : m % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hm_pos : 0 < m := by omega
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_ankeny_prime m hm_mod
  have : ∃ b : ℤ, b ^ 2 ≡ - (m : ℤ) [ZMOD (2 * q)] := exists_ankeny_b m q hm_mod hqp hq1 hq_mod
  obtain ⟨b, hb⟩ := this
  obtain ⟨x, y, z, h_rep, h_nz, hxy, hybz⟩ := exists_ankeny_representation m q b hm_pos hm_odd hqp hq1 hq_mod hb
  obtain ⟨u, v, h_final⟩ :=
    reduction_to_sum_three_squares m q x y z h_rep hqp hq1 hq_mod hm_odd hm_sq b hxy hybz
  use s * x.natAbs, s * u.natAbs, s * v.natAbs
  zify
  -- Keep this simp list minimal to avoid unused-simp-arg warnings.
  simp only [mul_pow, ← mul_add, sq_abs]
  have hm_eq_int : (n : ℤ) = s^2 * m := by exact_mod_cast hm_eq
  rw [← h_final, ← hm_eq_int]
  -- `ring` was previously here, but the goal is already closed after rewriting.

/-- Variant of the Ankeny/Minkowski route for the residue class `n ≡ 1 (mod 8)`.

This reuses the same lattice/ellipsoid setup (`2q` in the quadratic form) but swaps the Jacobi-symbol
computation step (see `exists_ankeny_b_one_mod_eight`). -/
