import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_four_thirds_window
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2)
    (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_scaled_central_power_gap n i (by omega) hi_half
    (scaled_power_gap_of_four_thirds_window hi_large hi_half hn_lower hn_upper)

end ScaledPowerDerivativeCriterion

