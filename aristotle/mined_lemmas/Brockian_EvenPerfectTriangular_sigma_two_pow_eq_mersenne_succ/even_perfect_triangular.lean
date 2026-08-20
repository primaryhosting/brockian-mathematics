import Mathlib

namespace Brockian.EvenPerfectTriangular

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number. -/

theorem even_perfect_triangular {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, n = k * (k + 1) / 2 := by
  obtain ⟨p, _hprime, rfl⟩ :=
    eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  refine ⟨mersenne (p + 1), ?_⟩
  rw [mersenne]
  have hpow : 1 ≤ 2 ^ (p + 1) := one_le_pow₀ (by omega)
  rw [Nat.sub_add_cancel hpow]
  have hdiv : 2 ∣ 2 ^ (p + 1) := by
    rw [pow_succ]
    exact dvd_mul_of_dvd_right (dvd_refl 2) (2 ^ p)
  rw [Nat.mul_div_assoc _ hdiv]
  norm_num [pow_succ]
  ac_rfl

end Brockian.EvenPerfectTriangular

