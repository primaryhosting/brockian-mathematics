import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma prime_coprime_210 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    p.Coprime 210 := by
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  have hdiv' : p ∣ 2 * (3 * (5 * 7)) := by
    simpa [show 210 = 2 * (3 * (5 * 7)) by norm_num] using hdiv
  rcases hp.dvd_mul.mp hdiv' with h2 | hrest
  · have hp_eq : p = 2 := by
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have hp_ge : 2 ≤ p := hp.two_le
      omega
    exact hp2 hp_eq
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · have hp_eq : p = 3 := by
      have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · rfl
    exact hp3 hp_eq
  rcases hp.dvd_mul.mp hrest with h5 | h7
  · have hp_eq : p = 5 := by
      have hp_le : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hp
      · rfl
    exact hp5 hp_eq
  · have hp_eq : p = 7 := by
      have hp_le : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hp
      · exact (hp5 rfl).elim
      · norm_num at hp
      · rfl
    exact hp7 hp_eq

