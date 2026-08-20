import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_twice
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hip, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul i (by omega)
  exact sylvester_schur_of_prime_in_top_interval n i (by omega)
    ⟨p, hp, by omega, by omega⟩

