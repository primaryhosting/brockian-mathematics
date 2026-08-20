import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma odd_not_three_dvd_has_prime_gt_three {j : ℕ} (hj_gt : 1 < j) (hj_odd : Odd j)
    (hj_not_three : ¬ 3 ∣ j) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpgt2, hpj⟩ := odd_has_prime_gt_two hj_gt hj_odd
  have hpgt3 : 3 < p := by
    by_contra hnot
    have hp_eq3 : p = 3 := by omega
    exact hj_not_three (hp_eq3 ▸ hpj)
  exact ⟨p, hp, hpgt3, hpj⟩

