import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_factorial_primorial_gap
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i.factorial * (n ^ n.sqrt * primorial i) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn : 0 < n := by omega
  have hm_pos : 0 < n - i + 1 := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial i :=
    choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime hn hi_half hno
  have htop : n - i + 1 + i - 1 = n := by omega
  have hasc_choose :
      (n - i + 1).ascFactorial i = i.factorial * Nat.choose n i := by
    simpa [htop] using ascFactorial_eq_factorial_mul_choose_start
      (m := n - i + 1) (k := i) hm_pos
  have hlower :
      (n - i + 1) ^ i ≤ i.factorial * Nat.choose n i := by
    simpa [hasc_choose] using pow_le_ascFactorial (n - i + 1) i
  have hupper_mul :
      i.factorial * Nat.choose n i ≤ i.factorial * (n ^ n.sqrt * primorial i) :=
    Nat.mul_le_mul_left i.factorial hupper
  exact (not_lt_of_ge (hlower.trans hupper_mul)) hgap

