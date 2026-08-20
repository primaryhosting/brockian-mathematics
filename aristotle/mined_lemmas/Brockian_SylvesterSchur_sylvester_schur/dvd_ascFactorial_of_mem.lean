import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma dvd_ascFactorial_of_mem {m k j : ℕ} (hlo : m ≤ j) (hhi : j < m + k) :
    j ∣ m.ascFactorial k := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      rw [Nat.ascFactorial_succ]
      by_cases hj : j = m + k
      · subst hj
        exact dvd_mul_right _ _
      · have hhi' : j < m + k := by omega
        exact dvd_mul_of_dvd_right (ih hhi') _

