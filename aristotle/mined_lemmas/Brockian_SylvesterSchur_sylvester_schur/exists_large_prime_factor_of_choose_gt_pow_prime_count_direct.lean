import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem exists_large_prime_factor_of_choose_gt_pow_prime_count_direct
    {N k : ℕ} (hkN : k ≤ N) (hN : 0 < N)
    (hgt : N ^ (k + 1).primesBelow.card < Nat.choose N k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ Nat.choose N k := by
  by_contra hno
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose N k → p < k + 1 := by
    intro p hp hp_choose
    by_contra hnot
    have hkp : k < p := by omega
    exact hno ⟨p, hp, hkp, hp_choose⟩
  have hle :
      Nat.choose N k ≤ N ^ (k + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hkN hN hsmall
  exact (not_lt_of_ge hle) hgt

