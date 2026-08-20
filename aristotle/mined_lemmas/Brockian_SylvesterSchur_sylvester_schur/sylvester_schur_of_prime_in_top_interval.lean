import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_prime_in_top_interval
    (n i : ℕ) (hi_half : i ≤ n / 2)
    (hprime : ∃ p : ℕ, p.Prime ∧ n - i < p ∧ p ≤ n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hnp, hpn⟩ := hprime
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hip : i < p := by omega
  have hp_mem : p ∈ Set.Ico (n - i + 1) (n + 1) := by
    constructor <;> omega
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hp_mem dvd_rfl⟩

