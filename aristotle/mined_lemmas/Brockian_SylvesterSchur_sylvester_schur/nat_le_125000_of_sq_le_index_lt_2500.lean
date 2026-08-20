import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma nat_le_125000_of_sq_le_index_lt_2500 {n i : ℕ} (hi2500 : i < 2500)
    (hn_sq : n ^ 2 ≤ i ^ 3) : n ≤ 125000 := by
  by_contra hnot
  have hn : 125001 ≤ n := by omega
  have hn_sq_ge : 125001 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hi_le : i ^ 3 ≤ 2499 ^ 3 := Nat.pow_le_pow_left (by omega : i ≤ 2499) 3
  have hnum : 2499 ^ 3 < 125001 ^ 2 := by norm_num
  omega

