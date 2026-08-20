import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma fact_div_cast (n k : ℕ) (h : k ≤ n) :
    ((n ! / k ! : ℕ) : ℝ) = (n ! : ℝ) / (k ! : ℝ) := by
  have hdvd : k ! ∣ n ! := Nat.factorial_dvd_factorial h
  have heq : k ! * (n ! / k !) = n ! := Nat.mul_div_cancel' hdvd
  field_simp
  exact mod_cast (mul_comm (k ! : ℕ) (n ! / k !) ▸ heq)

/-- Any integer combination of the numbers `n !/k !`, `k ≤ n`, is an integer. -/
