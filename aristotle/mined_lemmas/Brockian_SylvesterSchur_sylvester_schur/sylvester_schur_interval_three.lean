import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_three {m : ℕ} (hm : 3 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 3) ∧ p.Prime ∧ 3 < p ∧ p ∣ j := by
  have hr : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 6
  · have hodd : Odd (m + 1) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 1 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 1) (by omega) hodd hnot3
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd m := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m) (by omega) hodd hnot3
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hnot3m : ¬ 3 ∣ m := by intro hd; omega
    have hm2 : 2 < m := by omega
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm2 with h4m | hoddprime_m
    · have hnot3m2 : ¬ 3 ∣ m + 2 := by intro hd; omega
      have hm2_gt : 2 < m + 2 := by omega
      rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm2_gt with h4m2 | hoddprime_m2
      · obtain ⟨a, ha⟩ := h4m
        obtain ⟨b, hb⟩ := h4m2
        omega
      · obtain ⟨p, hp, hpj, hpodd⟩ := hoddprime_m2
        have hpgt : 3 < p := odd_prime_dvd_not_three_has_prime_gt_three hp hpj hpodd hnot3m2
        exact ⟨m + 2, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
    · obtain ⟨p, hp, hpj, hpodd⟩ := hoddprime_m
      have hpgt : 3 < p := odd_prime_dvd_not_three_has_prime_gt_three hp hpj hpodd hnot3m
      exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd (m + 2) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 2 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 2) (by omega) hodd hnot3
    exact ⟨m + 2, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd (m + 1) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 1 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 1) (by omega) hodd hnot3
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd m := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m) (by omega) hodd hnot3
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩

