import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_two {m : ℕ} (hm : 2 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 2) ∧ p.Prime ∧ 2 < p ∧ p ∣ j := by
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · have hodd : Odd (m + 1) := hm_even.add_one
    obtain ⟨p, hp, hpgt, hpj⟩ := odd_has_prime_gt_two (j := m + 1) (by omega) hodd
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · obtain ⟨p, hp, hpgt, hpj⟩ := odd_has_prime_gt_two (j := m) (by omega) hm_odd
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩

