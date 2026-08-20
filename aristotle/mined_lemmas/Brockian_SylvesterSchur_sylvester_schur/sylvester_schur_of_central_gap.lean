import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_central_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hprimorial : primorial (n / 3) ≤ 4 ^ (n / 3) :=
    primorial_le_4_pow (n / 3)
  have hgap' : i * (n ^ n.sqrt * primorial (n / 3)) < 4 ^ i := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left i (Nat.mul_le_mul_left (n ^ n.sqrt) hprimorial)) hgap
  exact sylvester_schur_of_central_primorial_gap n i hi hi_half hgap'

section FiveHalvesCentralGap

open Real

