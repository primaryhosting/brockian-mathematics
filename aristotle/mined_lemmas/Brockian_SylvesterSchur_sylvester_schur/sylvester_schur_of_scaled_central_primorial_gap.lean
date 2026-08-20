import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_scaled_central_primorial_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * (n ^ n.sqrt * primorial i)) < n ^ i * 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hn : 0 < n := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial i :=
    choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime hn hi_half hno
  have hscaled_lower :
      n ^ i * 4 ^ i < i * ((2 * i) ^ i * Nat.choose n i) := by
    calc
      n ^ i * 4 ^ i < n ^ i * (i * i.centralBinom) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.four_pow_lt_mul_centralBinom i hi)
          (Nat.pow_pos (a := n) (n := i) hn)
      _ = i * (n ^ i * i.centralBinom) := by ring
      _ ≤ i * ((2 * i) ^ i * Nat.choose n i) :=
        Nat.mul_le_mul_left i (pow_mul_centralBinom_le_pow_mul_choose_of_half hi_half)
  have hscaled_upper :
      i * ((2 * i) ^ i * Nat.choose n i) ≤
        i * ((2 * i) ^ i * (n ^ n.sqrt * primorial i)) := by
    exact Nat.mul_le_mul_left i (Nat.mul_le_mul_left ((2 * i) ^ i) hupper)
  exact (not_lt_of_ge (hscaled_lower.trans_le hscaled_upper).le) hgap

