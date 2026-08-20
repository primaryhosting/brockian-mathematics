import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_central_five_halves
    (n i : ℕ) (hi_large : 4410 ≤ i) (hi_half : i ≤ n / 2)
    (hn_le : 2 * n ≤ 5 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_central_gap n i (by omega) hi_half
    (central_gap_of_le_five_halves hi_large hi_half hn_le)

end FiveHalvesCentralGap

section ScaledPowerDerivativeGap

open Real

