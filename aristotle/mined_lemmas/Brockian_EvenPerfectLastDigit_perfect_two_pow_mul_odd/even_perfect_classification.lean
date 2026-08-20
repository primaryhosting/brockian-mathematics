import Mathlib

namespace Brockian.EvenPerfectLastDigit

/-- The core of the Euclid--Euler argument.  If the exact power of two in a
perfect number is `2^k`, its odd part is the corresponding Mersenne prime. -/

theorem even_perfect_classification {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ p : ℕ, Nat.Prime (2 ^ p - 1) ∧ n = 2 ^ (p - 1) * (2 ^ p - 1) := by
  rcases Nat.exists_eq_two_pow_mul_odd hp.2.ne' with ⟨k, m, hm, rfl⟩
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    exact (Nat.not_even_iff_odd.mpr hm) (by simpa using he)
  obtain ⟨hm_eq, hm_prime⟩ := perfect_two_pow_mul_odd hk hm hp
  refine ⟨k + 1, ?_, ?_⟩
  · simpa [hm_eq] using hm_prime
  · simp [hm_eq]

/-- A number in Euclid--Euler form has final decimal digit 6 or 8. -/
