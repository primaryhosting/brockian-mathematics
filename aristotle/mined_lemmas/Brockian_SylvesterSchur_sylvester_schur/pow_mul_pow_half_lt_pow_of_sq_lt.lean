import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_mul_pow_half_lt_pow_of_sq_lt {n i : ℕ} (hi : 0 < i) (hlarge : i ^ 2 < n) :
    i ^ i * n ^ (i / 2) < n ^ i := by
  let r := i / 2
  let d := i - r
  have hd_pos : 0 < d := by
    dsimp [d, r]
    omega
  have hi_exp_le : i ≤ 2 * d := by
    dsimp [d, r]
    omega
  have hi_pow_lt : i ^ i < n ^ d := by
    calc
      i ^ i ≤ i ^ (2 * d) := Nat.pow_le_pow_right hi hi_exp_le
      _ = (i ^ 2) ^ d := by rw [pow_mul]
      _ < n ^ d := Nat.pow_lt_pow_left hlarge hd_pos.ne'
  calc
    i ^ i * n ^ (i / 2) = i ^ i * n ^ r := by rfl
    _ < n ^ d * n ^ r :=
      Nat.mul_lt_mul_of_pos_right hi_pow_lt (Nat.pow_pos (a := n) (n := r) (by omega))
    _ = n ^ (d + r) := by rw [← pow_add]
    _ = n ^ i := by
      congr 1
      dsimp [d, r]
      omega

