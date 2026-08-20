import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma factorial_mul_pow_half_lt_of_quadratic_large {n i : ℕ} (hi : 8 ≤ i)
    (hi_half : i ≤ n / 2) (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    i.factorial * n ^ (i / 2) < (n - i + 1) ^ i := by
  let m := n - i + 1
  let r := i / 2
  let d := i - r
  have hi_pos : 0 < i := by omega
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hn_le : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hbase : 4 * i ^ 2 ≤ m := by simpa [m] using hm_large
  have hfac : i.factorial ≤ i ^ i := Nat.factorial_le_pow i
  have hn_pow : n ^ r ≤ (2 * m) ^ r := Nat.pow_le_pow_left hn_le r
  have hleft_le : i.factorial * n ^ r ≤ i ^ i * (2 * m) ^ r :=
    Nat.mul_le_mul hfac hn_pow
  have hleft_le' : i.factorial * n ^ r ≤ i ^ i * 2 ^ r * m ^ r := by
    calc
      i.factorial * n ^ r ≤ i ^ i * (2 * m) ^ r := hleft_le
      _ = i ^ i * (2 ^ r * m ^ r) := by rw [mul_pow]
      _ = i ^ i * 2 ^ r * m ^ r := by ring
  have h_i_exp : i ≤ 2 * d := by
    dsimp [d, r]
    omega
  have h_r_exp : r < 2 * d := by
    dsimp [d, r]
    omega
  have hprod_lt : i ^ i * 2 ^ r < i ^ (2 * d) * 2 ^ (2 * d) := by
    calc
      i ^ i * 2 ^ r ≤ i ^ (2 * d) * 2 ^ r :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hi_pos h_i_exp)
      _ < i ^ (2 * d) * 2 ^ (2 * d) :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) h_r_exp)
          (Nat.pow_pos (a := i) (n := 2 * d) hi_pos)
  have hbase_expand : i ^ (2 * d) * 2 ^ (2 * d) = (4 * i ^ 2) ^ d := by
    rw [mul_pow, show 4 = 2 ^ 2 by norm_num, pow_mul, pow_mul]
    ring
  have hmd : i ^ i * 2 ^ r < m ^ d := by
    calc
      i ^ i * 2 ^ r < i ^ (2 * d) * 2 ^ (2 * d) := hprod_lt
      _ = (4 * i ^ 2) ^ d := hbase_expand
      _ ≤ m ^ d := Nat.pow_le_pow_left hbase d
  calc
    i.factorial * n ^ (i / 2) = i.factorial * n ^ r := by rfl
    _ ≤ i ^ i * 2 ^ r * m ^ r := hleft_le'
    _ < m ^ d * m ^ r :=
      Nat.mul_lt_mul_of_pos_right hmd (Nat.pow_pos (a := m) (n := r) hm_pos)
    _ = m ^ (d + r) := by rw [← pow_add]
    _ = m ^ i := by
      congr 1
      dsimp [d, r]
      omega
    _ = (n - i + 1) ^ i := by rfl

