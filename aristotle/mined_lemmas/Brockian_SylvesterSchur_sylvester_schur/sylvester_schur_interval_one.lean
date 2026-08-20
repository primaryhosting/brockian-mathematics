import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_one {m : ℕ} (hm : 1 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 1) ∧ p.Prime ∧ 1 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  exact ⟨m, p, by simp, hp, hp.one_lt, hpm⟩

