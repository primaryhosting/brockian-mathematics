import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_power_gap
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hgap : i ^ i * n ^ r < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  by_contra hno
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose n i → p < i + 1 := by
    intro p hp hp_choose
    by_contra hnot
    have hip : i < p := by omega
    exact hno ⟨p, hp, hip, hp_choose⟩
  have hchoose_le_count :
      Nat.choose n i ≤ n ^ (i + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hi_le_n hn_pos hsmall
  have hchoose_le : Nat.choose n i ≤ n ^ r :=
    hchoose_le_count.trans (Nat.pow_le_pow_right hn_pos hr_count)
  have hlower : n ^ i ≤ i ^ i * Nat.choose n i :=
    pow_le_pow_mul_choose n i hi_le_n
  have hupper : i ^ i * Nat.choose n i ≤ i ^ i * n ^ r :=
    Nat.mul_le_mul_left _ hchoose_le
  exact (not_lt_of_ge (hlower.trans hupper)) hgap

