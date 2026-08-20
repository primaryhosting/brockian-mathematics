import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_twice_add_one
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (i + 1) (by omega)
  have hip : i < p := by omega
  have hp_ne_top : p ≠ 2 * (i + 1) := by
    intro htop
    have hp_ne_two : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
    have hp_even : Even p := by
      rw [htop]
      exact even_two_mul (i + 1)
    exact (Nat.not_even_iff_odd.mpr hp_odd) hp_even
  have hp_le_n : p ≤ n := by omega
  exact sylvester_schur_of_prime_in_top_interval n i (by omega)
    ⟨p, hp, by omega, hp_le_n⟩

/-- A finite prime-gap certificate for the small residual range. -/
