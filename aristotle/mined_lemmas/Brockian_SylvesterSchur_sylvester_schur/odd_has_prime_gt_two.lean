import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma odd_has_prime_gt_two {j : ℕ} (hj_gt : 1 < j) (hj_odd : Odd j) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpj⟩ := Nat.exists_prime_and_dvd (by omega : j ≠ 1)
  have hnot_two_dvd : ¬ 2 ∣ j := by
    intro h2
    have hev : Even j := (even_iff_two_dvd).mpr h2
    exact (Nat.not_even_iff_odd.mpr hj_odd) hev
  have hp_gt : 2 < p := by
    by_contra hnot
    have hp_two_le : 2 ≤ p := hp.two_le
    have hp_eq : p = 2 := by omega
    exact hnot_two_dvd (hp_eq ▸ hpj)
  exact ⟨p, hp, hp_gt, hpj⟩

