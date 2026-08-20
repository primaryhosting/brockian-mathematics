import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma succ_pow_mul_sub_le_pow_mul_succ {N r : ℕ} (hr : r ≤ N + 1) :
    (N + 1) ^ r * (N + 1 - r) ≤ N ^ r * (N + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hr' : r ≤ N + 1 := by omega
      have ih' := ih hr'
      have hsub : N + 1 - (r + 1) = N - r := by omega
      have hsub2 : N + 1 - r = N - r + 1 := by omega
      have hmul_step : (N + 1) * (N - r) ≤ N * (N + 1 - r) := by
        rw [hsub2, Nat.mul_add, Nat.mul_one, Nat.succ_mul]
        exact Nat.add_le_add_left (Nat.sub_le N r) (N * (N - r))
      calc
        (N + 1) ^ (r + 1) * (N + 1 - (r + 1))
            = (N + 1) ^ r * ((N + 1) * (N - r)) := by
              rw [pow_succ, hsub]
              ring
        _ ≤ (N + 1) ^ r * (N * (N + 1 - r)) :=
              Nat.mul_le_mul_left _ hmul_step
        _ = ((N + 1) ^ r * (N + 1 - r)) * N := by ring
        _ ≤ (N ^ r * (N + 1)) * N := Nat.mul_le_mul_right _ ih'
        _ = N ^ (r + 1) * (N + 1) := by
              rw [pow_succ]
              ring

