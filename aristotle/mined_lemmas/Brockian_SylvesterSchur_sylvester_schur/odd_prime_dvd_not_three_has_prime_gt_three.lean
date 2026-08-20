import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma odd_prime_dvd_not_three_has_prime_gt_three {j p : ℕ} (hp : p.Prime) (hpj : p ∣ j)
    (hp_odd : Odd p) (hj_not_three : ¬ 3 ∣ j) : 3 < p := by
  by_contra hnot
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    norm_num [Nat.odd_iff] at hp_odd
  have hp_eq3 : p = 3 := by omega
  exact hj_not_three (hp_eq3 ▸ hpj)

