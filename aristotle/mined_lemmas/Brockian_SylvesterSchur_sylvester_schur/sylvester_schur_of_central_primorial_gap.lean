import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_of_central_primorial_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * (n ^ n.sqrt * primorial (n / 3)) < 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hn : 0 < n := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial (n / 3) :=
    choose_le_pow_sqrt_mul_primorial_third_of_no_large_prime hn hi_half hno
  have hcentral_le : i.centralBinom ≤ Nat.choose n i :=
    centralBinom_le_choose_of_half hi_half
  have hlower : 4 ^ i < i * Nat.choose n i :=
    (Nat.four_pow_lt_mul_centralBinom i hi).trans_le
      (Nat.mul_le_mul_left i hcentral_le)
  have hupper_mul :
      i * Nat.choose n i ≤ i * (n ^ n.sqrt * primorial (n / 3)) :=
    Nat.mul_le_mul_left i hupper
  exact (not_lt_of_ge (hlower.trans_le hupper_mul).le) hgap

