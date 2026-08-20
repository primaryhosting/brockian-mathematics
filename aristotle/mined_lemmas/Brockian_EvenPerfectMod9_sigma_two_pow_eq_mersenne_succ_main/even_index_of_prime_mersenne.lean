import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/

theorem even_index_of_prime_mersenne {k : ℕ}
    (hk : 1 < k) (hp : Nat.Prime (mersenne (k + 1))) : Even k := by
  have hpk : Nat.Prime (k + 1) := hp.of_mersenne
  have hn : ¬ Even (k + 1) := by
    rw [hpk.even_iff]
    omega
  rw [Nat.even_add_one] at hn
  exact Classical.byContradiction hn

/-- The Euclid--Euler expression has residue one modulo nine at every even index. -/
