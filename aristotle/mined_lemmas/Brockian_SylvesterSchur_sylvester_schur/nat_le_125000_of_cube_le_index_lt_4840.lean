import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma nat_le_125000_of_cube_le_index_lt_4840 {n i : ℕ} (hi4840 : i < 4840)
    (hn_cube : n ^ 3 ≤ i ^ 4) : n ≤ 125000 := by
  by_contra hnot
  have hn : 125001 ≤ n := by omega
  have hn_cube_ge : 125001 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hi_le : i ^ 4 ≤ 4839 ^ 4 := Nat.pow_le_pow_left (by omega : i ≤ 4839) 4
  have hnum : 4839 ^ 4 < 125001 ^ 3 := by norm_num
  omega

