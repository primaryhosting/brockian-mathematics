import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/

theorem eq_two_pow_mul_odd_main {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- Euler's classification of even perfect numbers, reconstructed using only
main-library APIs. -/
