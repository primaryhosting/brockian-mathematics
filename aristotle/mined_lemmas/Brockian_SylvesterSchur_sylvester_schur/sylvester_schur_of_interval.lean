import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_interval
    (hSS : SylvesterSchurInterval)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm : i < n - i + 1 := by omega
  obtain ⟨j, p, hj, hp, hip, hpj⟩ := hSS hi_pos hm
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj' : j ∈ Set.Ico (n - i + 1) (n + 1) := by
    simpa [htop] using hj
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hj' hpj⟩

