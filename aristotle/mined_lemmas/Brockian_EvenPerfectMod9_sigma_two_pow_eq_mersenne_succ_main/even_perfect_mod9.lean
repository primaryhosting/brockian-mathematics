import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/

theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) :
    n % 9 = 1 := by
  obtain ⟨k, hprime, rfl⟩ :=
    eq_two_pow_mul_prime_mersenne_of_even_perfect_main he hp
  apply even_euclid_euler_mod9
  apply even_index_of_prime_mersenne (hp := hprime)
  by_contra hnot
  interval_cases k <;> norm_num [mersenne] at h6

end Brockian.EvenPerfectMod9

