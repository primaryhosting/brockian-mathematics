import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, 0, 0, by simp⟩
  obtain ⟨a, t, hn, _ht4, ht7⟩ := exists_four_pow_mul_reduced n hn0 h
  -- After peeling off powers of `4`, the remaining factor `t` satisfies `t % 8 ≠ 7`.
  by_cases ht3 : t % 8 = 3
  · have ht_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = t :=
      sum_three_squares_of_three_mod_eight t ht3
    have hn_rep :
        ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t :=
      sum_three_squares_mul_sq (2 ^ a) t ht_rep
    rcases hn_rep with ⟨x, y, z, hxyz⟩
    refine ⟨x, y, z, ?_⟩
    have hpow : (2 ^ a) ^ 2 = 4 ^ a := by
      -- `(2^a)^2 = 2^(a*2)` and `4^a = (2^2)^a = 2^(2*a)`.
      -- Keep it explicit to avoid `simp` loops in downstream glue.
      calc
        (2 ^ a) ^ 2 = 2 ^ (a * 2) := by simp [pow_mul]
        _ = 2 ^ (2 * a) := by simp [Nat.mul_comm]
        _ = (2 ^ 2) ^ a := by simp [pow_mul]
        _ = 4 ^ a := by simp [pow_two]
    calc
      x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t := hxyz
      _ = 4 ^ a * t := by simp [hpow]
      _ = n := hn.symm
  ·
    -- Now `t % 8 ≠ 3`. At this point we are in the “reduced” situation:
    -- - `4 ∤ t` (by construction), and
    -- - `t % 8 ≠ 7` (mod-8 obstruction already discharged).
    --
    -- The remaining residue classes are exactly `t % 8 ∈ {1,2,5,6}`.
    --
    -- At this point we dispatch by residue class:
    -- - `t % 8 = 1`: Ankeny/Minkowski (Q route)
    -- - `t % 8 ∈ {2,5,6}`: Q₁ route (see `sum_three_squares_of_*_mod_eight` lemmas above)
    have ht_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = t := by
      by_cases ht1 : t % 8 = 1
      · exact sum_three_squares_of_one_mod_eight t ht1
      by_cases ht2 : t % 8 = 2
      · exact sum_three_squares_of_two_mod_eight t ht2
      by_cases ht5 : t % 8 = 5
      · exact sum_three_squares_of_five_mod_eight t ht5
      -- only remaining reduced residue is `6 mod 8`
      have ht6 : t % 8 = 6 :=
        mod8_eq_six_of_reduced t _ht4 ht7 ht3 ht1 ht2 ht5
      exact sum_three_squares_of_six_mod_eight t ht6
    have hn_rep :
        ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t :=
      sum_three_squares_mul_sq (2 ^ a) t ht_rep
    rcases hn_rep with ⟨x, y, z, hxyz⟩
    refine ⟨x, y, z, ?_⟩
    have hpow : (2 ^ a) ^ 2 = 4 ^ a := by
      calc
        (2 ^ a) ^ 2 = 2 ^ (a * 2) := by simp [pow_mul]
        _ = 2 ^ (2 * a) := by simp [Nat.mul_comm]
        _ = (2 ^ 2) ^ a := by simp [pow_mul]
        _ = 4 ^ a := by simp [pow_two]
    calc
      x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t := hxyz
      _ = 4 ^ a * t := by simp [hpow]
      _ = n := hn.symm

/-- Legendre's three-square theorem, in the repo's preferred “exception” formulation. -/
