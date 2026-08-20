import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_scaled_central_power_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hgap' :
      i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i := by
    calc
      i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i))
          = (i * ((2 * i) ^ i * n ^ n.sqrt)) * 4 ^ i := by ring
      _ < n ^ i * 4 ^ i :=
          Nat.mul_lt_mul_of_pos_right hgap
            (Nat.pow_pos (a := 4) (n := i) (by norm_num))
  exact sylvester_schur_of_scaled_central_gap n i hi hi_half hgap'

section ScaledPowerDerivativeCriterion

open Real

