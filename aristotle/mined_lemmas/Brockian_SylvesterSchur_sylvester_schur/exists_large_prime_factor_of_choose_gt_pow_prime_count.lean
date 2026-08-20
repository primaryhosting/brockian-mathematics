import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem exists_large_prime_factor_of_choose_gt_pow_prime_count
    {m k : ℕ} (hk : 0 < k) (hm : k < m)
    (hgt : (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_contra hno
  have hno' :
      ∀ j p : ℕ, j ∈ Set.Ico m (m + k) → p.Prime → k < p → p ∣ j → False := by
    intro j p hj hp hkp hpj
    exact hno ⟨j, p, hj, hp, hkp, hpj⟩
  have hm_pos : 0 < m := by omega
  have hN_pos : 0 < m + k - 1 := by omega
  have hkN : k ≤ m + k - 1 := by omega
  have hasc_choose : m.ascFactorial k = k.factorial * Nat.choose (m + k - 1) k := by
    have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    have hm_add : m - 1 + k = m + k - 1 := by omega
    simpa [hm_sub, hm_add] using Nat.ascFactorial_eq_factorial_mul_choose (m - 1) k
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose (m + k - 1) k → p < k + 1 := by
    intro p hp hp_choose
    have hp_asc : p ∣ m.ascFactorial k := by
      rw [hasc_choose]
      exact dvd_mul_of_dvd_right hp_choose k.factorial
    obtain ⟨j, hj, hpj⟩ := exists_mem_Ico_dvd_of_prime_dvd_ascFactorial hp hp_asc
    have hpk : p ≤ k := by
      by_contra hnot
      exact hno' j p hj hp (Nat.lt_of_not_ge hnot) hpj
    exact Nat.lt_succ_iff.mpr hpk
  have hle :
      Nat.choose (m + k - 1) k ≤ (m + k - 1) ^ (k + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hkN hN_pos hsmall
  exact (not_lt_of_ge hle) hgt

