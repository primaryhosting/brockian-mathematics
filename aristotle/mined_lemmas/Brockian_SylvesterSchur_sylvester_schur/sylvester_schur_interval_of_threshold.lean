import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem sylvester_schur_interval_of_threshold
    (hbase : SylvesterSchurIntervalThreshold) :
    SylvesterSchurInterval := by
  intro m k hk hm
  obtain ⟨m₀, hm₀, hineq₀, hbelow⟩ := hbase k hk
  by_cases hle : m₀ ≤ m
  · exact exists_large_prime_factor_of_choose_gt_pow_prime_count hk hm
      (choose_inequality_of_ge_start hk hm₀ hle hineq₀)
  · exact hbelow m hm (Nat.lt_of_not_ge hle)

