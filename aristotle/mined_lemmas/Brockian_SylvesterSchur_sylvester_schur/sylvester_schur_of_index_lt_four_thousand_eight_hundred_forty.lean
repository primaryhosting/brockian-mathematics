import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi49 : 49 ≤ i) (hi_lt : i < 4840) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hi72 : i < 72
  · by_cases hcube : i ^ 3 < n ^ 2
    · exact sylvester_schur_of_cube_lt_square n i hi49 hi_half hcube
    · have hn_sq : n ^ 2 ≤ i ^ 3 := Nat.le_of_not_gt hcube
      have hn_le : n ≤ 600 := nat_le_600_of_sq_le_small hi49 hi72 hn_sq
      obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_49_le_of_le_600 n (by omega) hn_le
      exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩
  · have hi72le : 72 ≤ i := by omega
    by_cases hi2500 : i < 2500
    · by_cases hcube : i ^ 3 < n ^ 2
      · exact sylvester_schur_of_cube_lt_square n i hi49 hi_half hcube
      · have hn_sq : n ^ 2 ≤ i ^ 3 := Nat.le_of_not_gt hcube
        have hn_le : n ≤ 125000 := nat_le_125000_of_sq_le_index_lt_2500 hi2500 hn_sq
        obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_72_le_of_le_125000 n (by omega) hn_le
        exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩
    · have hi2500le : 2500 ≤ i := by omega
      by_cases hfourth : i ^ 4 < n ^ 3
      · exact sylvester_schur_of_fourth_lt_cube n i hi2500le hi_half hfourth
      · have hn_cube : n ^ 3 ≤ i ^ 4 := Nat.le_of_not_gt hfourth
        have hn_le : n ≤ 125000 := nat_le_125000_of_cube_le_index_lt_4840 hi_lt hn_cube
        obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_72_le_of_le_125000 n (by omega) hn_le
        exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩

