import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma ascFactorial_eq_factorial_mul_choose_start {m k : ℕ} (hm : 0 < m) :
    m.ascFactorial k = k.factorial * Nat.choose (m + k - 1) k := by
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have hm_add : m - 1 + k = m + k - 1 := by omega
  simpa [hm_sub, hm_add] using Nat.ascFactorial_eq_factorial_mul_choose (m - 1) k

