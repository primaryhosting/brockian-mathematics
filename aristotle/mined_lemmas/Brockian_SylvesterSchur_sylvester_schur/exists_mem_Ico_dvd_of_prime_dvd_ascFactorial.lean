import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma exists_mem_Ico_dvd_of_prime_dvd_ascFactorial {m k p : ℕ}
    (hp : p.Prime) (h : p ∣ m.ascFactorial k) :
    ∃ j : ℕ, j ∈ Set.Ico m (m + k) ∧ p ∣ j := by
  induction k with
  | zero =>
      rw [Nat.ascFactorial_zero] at h
      exact (hp.not_dvd_one h).elim
  | succ k ih =>
      rw [Nat.ascFactorial_succ] at h
      rcases hp.dvd_mul.mp h with hp_dvd | hp_dvd
      · exact ⟨m + k, ⟨by omega, by omega⟩, hp_dvd⟩
      · obtain ⟨j, hj, hpj⟩ := ih hp_dvd
        have hhi : j < m + Nat.succ k := by
          have : j < m + k := hj.2
          omega
        exact ⟨j, ⟨hj.1, hhi⟩, hpj⟩

