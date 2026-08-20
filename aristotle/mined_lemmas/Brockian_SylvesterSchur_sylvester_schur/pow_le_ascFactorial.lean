import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_le_ascFactorial (m k : ℕ) : m ^ k ≤ m.ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.ascFactorial_succ, pow_succ]
      calc
        m ^ k * m ≤ m.ascFactorial k * (m + k) := Nat.mul_le_mul ih (Nat.le_add_right m k)
        _ = (m + k) * m.ascFactorial k := by ring

