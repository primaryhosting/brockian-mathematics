import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma sylvester_schur_interval_le_forty_eight {m k : ℕ} (hk : 0 < k) (hk48 : k ≤ 48)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk20 : k ≤ 20
  · exact sylvester_schur_interval_le_twenty hk hk20 hm
  · interval_cases k
    · by_cases hle : 29 ≤ m
      · have hineq0 : (29 + 21 - 1) ^ (21 + 1).primesBelow.card < Nat.choose (29 + 21 - 1) 21 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 21) (m₀ := 29) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 21)
          (by omega) hm hineq
      · have hlt : m < 29 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 28 ≤ m
      · have hineq0 : (28 + 22 - 1) ^ (22 + 1).primesBelow.card < Nat.choose (28 + 22 - 1) 22 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 22) (m₀ := 28) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 22)
          (by omega) hm hineq
      · have hlt : m < 28 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 36 ≤ m
      · have hineq0 : (36 + 23 - 1) ^ (23 + 1).primesBelow.card < Nat.choose (36 + 23 - 1) 23 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 23) (m₀ := 36) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 23)
          (by omega) hm hineq
      · have hlt : m < 36 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 34 ≤ m
      · have hineq0 : (34 + 24 - 1) ^ (24 + 1).primesBelow.card < Nat.choose (34 + 24 - 1) 24 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 24) (m₀ := 34) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 24)
          (by omega) hm hineq
      · have hlt : m < 34 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 32 ≤ m
      · have hineq0 : (32 + 25 - 1) ^ (25 + 1).primesBelow.card < Nat.choose (32 + 25 - 1) 25 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 25) (m₀ := 32) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 25)
          (by omega) hm hineq
      · have hlt : m < 32 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 31 ≤ m
      · have hineq0 : (31 + 26 - 1) ^ (26 + 1).primesBelow.card < Nat.choose (31 + 26 - 1) 26 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 26) (m₀ := 31) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 26)
          (by omega) hm hineq
      · have hlt : m < 31 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 30 ≤ m
      · have hineq0 : (30 + 27 - 1) ^ (27 + 1).primesBelow.card < Nat.choose (30 + 27 - 1) 27 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 27) (m₀ := 30) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 27)
          (by omega) hm hineq
      · have hlt : m < 30 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 29 ≤ m
      · have hineq0 : (29 + 28 - 1) ^ (28 + 1).primesBelow.card < Nat.choose (29 + 28 - 1) 28 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 28) (m₀ := 29) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 28)
          (by omega) hm hineq
      · have hlt : m < 29 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 36 ≤ m
      · have hineq0 : (36 + 29 - 1) ^ (29 + 1).primesBelow.card < Nat.choose (36 + 29 - 1) 29 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 29) (m₀ := 36) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 29)
          (by omega) hm hineq
      · have hlt : m < 36 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 35 ≤ m
      · have hineq0 : (35 + 30 - 1) ^ (30 + 1).primesBelow.card < Nat.choose (35 + 30 - 1) 30 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 30) (m₀ := 35) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 30)
          (by omega) hm hineq
      · have hlt : m < 35 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 43 ≤ m
      · have hineq0 : (43 + 31 - 1) ^ (31 + 1).primesBelow.card < Nat.choose (43 + 31 - 1) 31 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 31) (m₀ := 43) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 31)
          (by omega) hm hineq
      · have hlt : m < 43 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 41 ≤ m
      · have hineq0 : (41 + 32 - 1) ^ (32 + 1).primesBelow.card < Nat.choose (41 + 32 - 1) 32 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 32) (m₀ := 41) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 32)
          (by omega) hm hineq
      · have hlt : m < 41 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 40 ≤ m
      · have hineq0 : (40 + 33 - 1) ^ (33 + 1).primesBelow.card < Nat.choose (40 + 33 - 1) 33 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 33) (m₀ := 40) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 33)
          (by omega) hm hineq
      · have hlt : m < 40 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 39 ≤ m
      · have hineq0 : (39 + 34 - 1) ^ (34 + 1).primesBelow.card < Nat.choose (39 + 34 - 1) 34 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 34) (m₀ := 39) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 34)
          (by omega) hm hineq
      · have hlt : m < 39 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 38 ≤ m
      · have hineq0 : (38 + 35 - 1) ^ (35 + 1).primesBelow.card < Nat.choose (38 + 35 - 1) 35 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 35) (m₀ := 38) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 35)
          (by omega) hm hineq
      · have hlt : m < 38 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 37 ≤ m
      · have hineq0 : (37 + 36 - 1) ^ (36 + 1).primesBelow.card < Nat.choose (37 + 36 - 1) 36 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 36) (m₀ := 37) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 36)
          (by omega) hm hineq
      · have hlt : m < 37 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 44 ≤ m
      · have hineq0 : (44 + 37 - 1) ^ (37 + 1).primesBelow.card < Nat.choose (44 + 37 - 1) 37 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 37) (m₀ := 44) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 37)
          (by omega) hm hineq
      · have hlt : m < 44 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 43 ≤ m
      · have hineq0 : (43 + 38 - 1) ^ (38 + 1).primesBelow.card < Nat.choose (43 + 38 - 1) 38 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 38) (m₀ := 43) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 38)
          (by omega) hm hineq
      · have hlt : m < 43 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 42 ≤ m
      · have hineq0 : (42 + 39 - 1) ^ (39 + 1).primesBelow.card < Nat.choose (42 + 39 - 1) 39 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 39) (m₀ := 42) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 39)
          (by omega) hm hineq
      · have hlt : m < 42 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 41 ≤ m
      · have hineq0 : (41 + 40 - 1) ^ (40 + 1).primesBelow.card < Nat.choose (41 + 40 - 1) 40 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 40) (m₀ := 41) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 40)
          (by omega) hm hineq
      · have hlt : m < 41 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 48 ≤ m
      · have hineq0 : (48 + 41 - 1) ^ (41 + 1).primesBelow.card < Nat.choose (48 + 41 - 1) 41 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 41) (m₀ := 48) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 41)
          (by omega) hm hineq
      · have hlt : m < 48 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 47 ≤ m
      · have hineq0 : (47 + 42 - 1) ^ (42 + 1).primesBelow.card < Nat.choose (47 + 42 - 1) 42 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 42) (m₀ := 47) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 42)
          (by omega) hm hineq
      · have hlt : m < 47 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 55 ≤ m
      · have hineq0 : (55 + 43 - 1) ^ (43 + 1).primesBelow.card < Nat.choose (55 + 43 - 1) 43 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 43) (m₀ := 55) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 43)
          (by omega) hm hineq
      · have hlt : m < 55 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 54 ≤ m
      · have hineq0 : (54 + 44 - 1) ^ (44 + 1).primesBelow.card < Nat.choose (54 + 44 - 1) 44 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 44) (m₀ := 54) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 44)
          (by omega) hm hineq
      · have hlt : m < 54 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 53 ≤ m
      · have hineq0 : (53 + 45 - 1) ^ (45 + 1).primesBelow.card < Nat.choose (53 + 45 - 1) 45 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 45) (m₀ := 53) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 45)
          (by omega) hm hineq
      · have hlt : m < 53 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 51 ≤ m
      · have hineq0 : (51 + 46 - 1) ^ (46 + 1).primesBelow.card < Nat.choose (51 + 46 - 1) 46 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 46) (m₀ := 51) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 46)
          (by omega) hm hineq
      · have hlt : m < 51 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 60 ≤ m
      · have hineq0 : (60 + 47 - 1) ^ (47 + 1).primesBelow.card < Nat.choose (60 + 47 - 1) 47 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 47) (m₀ := 60) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 47)
          (by omega) hm hineq
      · have hlt : m < 60 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 58 ≤ m
      · have hineq0 : (58 + 48 - 1) ^ (48 + 1).primesBelow.card < Nat.choose (58 + 48 - 1) 48 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 48) (m₀ := 58) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 48)
          (by omega) hm hineq
      · have hlt : m < 58 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

