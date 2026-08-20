import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hi48 : i ≤ 48
  · exact sylvester_schur_of_index_le_forty_eight n i hi hi_half hi48
  by_cases hi4840 : 4840 ≤ i
  · exact sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty n i hi4840 hi_half
  exact sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty n i
    (by omega) (by omega) hi_half
end Erdos699Formalization

