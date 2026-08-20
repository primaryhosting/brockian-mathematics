import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hcentral : 2 * n ≤ 5 * i
  · exact sylvester_schur_of_central_five_halves n i (by omega) hi_half hcentral
  · have hn_lower : 5 * i ≤ 2 * n := by omega
    by_cases htop : i ^ 4 < n ^ 3
    · exact sylvester_schur_of_fourth_lt_cube n i (by omega) hi_half htop
    · exact sylvester_schur_of_four_thirds_window n i hi_large hi_half hn_lower
        (Nat.le_of_not_gt htop)

