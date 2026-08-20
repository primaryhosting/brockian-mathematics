import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_interval_of_small_start
    (hsmall : SylvesterSchurSmallStart) : SylvesterSchurInterval := by
  intro m k hk hm
  by_cases hk_one : k = 1
  · subst hk_one
    exact sylvester_schur_interval_one (m := m) hm
  · have hk_gt_one : 1 < k := by omega
    by_cases hlarge : k.factorial * 2 ^ (k - 1) < m
    · exact sylvester_schur_interval_of_large_start hk_gt_one hm hlarge
    · exact hsmall hk_gt_one hm (Nat.le_of_not_gt hlarge)

