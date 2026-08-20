import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_le_pow_sqrt_mul_primorial_third_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk_half : k ≤ n / 2)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ Nat.choose n k) :
    Nat.choose n k ≤ n ^ n.sqrt * primorial (n / 3) := by
  classical
  have hk_le_n : k ≤ n := le_trans hk_half (Nat.div_le_self n 2)
  let S : Finset ℕ := (Finset.range (n + 1)).filter fun p => p.Prime
  let small : Finset ℕ := S.filter fun p => p ≤ n.sqrt
  let medium : Finset ℕ := S.filter fun p => ¬ p ≤ n.sqrt
  let supportedMedium : Finset ℕ := medium.filter fun p => p ≤ n / 3
  let f := fun p : ℕ => p ^ (Nat.choose n k).factorization p
  have hchoose_prod : Nat.choose n k = ∏ p ∈ S, f p := by
    symm
    calc
      ∏ p ∈ S, f p = ∏ p ∈ Finset.range (n + 1), f p := by
        dsimp [S]
        exact Finset.prod_filter_of_ne fun p _ hp_ne_one => by
          by_contra hp_not_prime
          exact hp_ne_one (by simp [f, Nat.factorization_eq_zero_of_not_prime _ hp_not_prime])
      _ = Nat.choose n k := Nat.prod_pow_factorization_choose n k hk_le_n
  have hsmall_card : small.card ≤ n.sqrt := by
    have hsubset : small ⊆ Finset.Icc 1 n.sqrt := by
      intro p hp
      rw [Finset.mem_Icc]
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hple : p ≤ n.sqrt := (Finset.mem_filter.mp hp).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨hp_prime.one_lt.le, hple⟩
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 1 n.sqrt).card = n.sqrt := by
      rw [Nat.card_Icc]
      omega
    simpa [hIcc] using hcard
  have hsmall_le : ∏ p ∈ small, f p ≤ n ^ n.sqrt := by
    calc
      ∏ p ∈ small, f p ≤ ∏ _p ∈ small, n := by
        refine Finset.prod_le_prod' ?_
        intro p _hp
        exact Nat.pow_factorization_choose_le hn
      _ = n ^ small.card := by rw [Finset.prod_const]
      _ ≤ n ^ n.sqrt := Nat.pow_le_pow_right hn hsmall_card
  have hmedium_eq_supported : ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_medium hp_not_supported
    have hp_not_third : ¬ p ≤ n / 3 := by
      intro hp_third
      exact hp_not_supported (Finset.mem_filter.mpr ⟨hp_medium, hp_third⟩)
    have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
    have hp_not_small : ¬ p ≤ n.sqrt := (Finset.mem_filter.mp hp_medium).2
    have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
    by_cases hkp : k < p
    · have hfac : (Nat.choose n k).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (hno p hp_prime hkp)
      simp [f, hfac]
    · have hpk : p ≤ k := Nat.le_of_not_gt hkp
      have hpnk : p ≤ n - k := by omega
      have hp_ne_two : p ≠ 2 := by
        intro hp_two
        subst p
        have h4n : 4 ≤ n := by omega
        have hsqrt : 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using h4n)
        exact hp_not_small hsqrt
      have hn_lt_3p : n < 3 * p := by
        have hp_gt_third : n / 3 < p := Nat.lt_of_not_ge hp_not_third
        rwa [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3), mul_comm] at hp_gt_third
      have hfac : (Nat.choose n k).factorization p = 0 :=
        Nat.factorization_choose_of_lt_three_mul hp_ne_two hpk hpnk hn_lt_3p
      simp [f, hfac]
  have hmedium_le : ∏ p ∈ medium, f p ≤ primorial (n / 3) := by
    have hsupp_le : ∏ p ∈ supportedMedium, f p ≤ ∏ p ∈ supportedMedium, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_not_small : ¬ p ≤ n.sqrt := (Finset.mem_filter.mp hp_medium).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      have hp_large : n < p ^ 2 := Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small)
      have hfac_le : (Nat.choose n k).factorization p ≤ 1 :=
        Nat.factorization_choose_le_one hp_large
      exact (Nat.pow_le_pow_right hp_prime.one_lt.le hfac_le).trans_eq (by rw [pow_one])
    have hsupp_subset :
        supportedMedium ⊆ (Finset.range (n / 3 + 1)).filter fun p => p.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range]
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hp_third : p ≤ n / 3 := (Finset.mem_filter.mp hp).2
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨Nat.lt_succ_iff.mpr hp_third, hp_prime⟩
    have hprimorial :
        ∏ p ∈ supportedMedium, p ≤ primorial (n / 3) := by
      simpa [primorial] using
        (Finset.prod_le_prod_of_subset_of_one_le' (f := fun p : ℕ => p) hsupp_subset
          (fun p hp hp_not => by
            have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
            exact hp_prime.one_lt.le))
    calc
      ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := hmedium_eq_supported
      _ ≤ ∏ p ∈ supportedMedium, p := hsupp_le
      _ ≤ primorial (n / 3) := hprimorial
  calc
    Nat.choose n k = ∏ p ∈ S, f p := hchoose_prod
    _ = (∏ p ∈ small, f p) * ∏ p ∈ medium, f p := by
      dsimp [small, medium]
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ n ^ n.sqrt * primorial (n / 3) := Nat.mul_le_mul hsmall_le hmedium_le

