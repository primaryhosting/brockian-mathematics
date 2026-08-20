import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma nat_le_600_of_sq_le_small {n i : ℕ} (hi49 : 49 ≤ i) (hi72 : i < 72)
    (hn_sq : n ^ 2 ≤ i ^ 3) : n ≤ 600 := by
  by_contra hnot
  have hn601 : 601 ≤ n := by omega
  have hn_sq_ge : 601 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn601 2
  have hi_le : i ^ 3 ≤ 71 ^ 3 := Nat.pow_le_pow_left (by omega : i ≤ 71) 3
  have hnum : 71 ^ 3 < 601 ^ 2 := by norm_num
  omega

