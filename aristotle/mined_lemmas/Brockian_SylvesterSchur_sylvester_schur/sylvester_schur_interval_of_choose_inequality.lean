import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_interval_of_choose_inequality
    (hineq : SylvesterSchurChooseInequality) :
    SylvesterSchurInterval := by
  intro m k hk hm
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count hk hm (hineq hk hm)

