import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_mul_centralBinom_le_pow_mul_choose_of_half
    {n i : ℕ} (hi_half : i ≤ n / 2) :
    n ^ i * i.centralBinom ≤ (2 * i) ^ i * Nat.choose n i := by
  have htwice : 2 * i ≤ n := by omega
  have hm_pos : 0 < n - i + 1 := by omega
  have htop : n - i + 1 + i - 1 = n := by omega
  have hratio :=
    pow_mul_ascFactorial_le_pow_mul_ascFactorial_of_twice_le (n := n) (i := i) htwice
  refine Nat.le_of_mul_le_mul_left ?_ i.factorial_pos
  calc
    i.factorial * (n ^ i * i.centralBinom)
        = n ^ i * (i.factorial * i.centralBinom) := by ring
    _ = n ^ i * (i + 1).ascFactorial i := by
          rw [Nat.centralBinom, Nat.ascFactorial_eq_factorial_mul_choose, two_mul]
    _ ≤ (2 * i) ^ i * (n - i + 1).ascFactorial i := hratio
    _ = (2 * i) ^ i * (i.factorial * Nat.choose n i) := by
          rw [ascFactorial_eq_factorial_mul_choose_start (m := n - i + 1) (k := i) hm_pos,
            htop]
    _ = i.factorial * ((2 * i) ^ i * Nat.choose n i) := by ring

