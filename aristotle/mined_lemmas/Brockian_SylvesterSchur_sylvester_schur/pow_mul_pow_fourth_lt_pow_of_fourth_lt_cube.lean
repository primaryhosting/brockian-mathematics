import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hlarge : i ^ 4 < n ^ 3) :
    i ^ i * n ^ (i / 4) < n ^ i := by
  let q := i / 4
  have hn_pos : 0 < n := lt_trans hi hin
  have hmod_lt : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  have hdivmod : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
  have hi_pow_lt : i ^ i < n ^ (i - q) := by
    interval_cases hmod : i % 4
    · have hi_eq : i = 4 * q := by
        dsimp [q] at *
        omega
      have hq_pos : 0 < q := by omega
      calc
        i ^ i = (i ^ 4) ^ q := by
          rw [hi_eq, pow_mul]
        _ < (n ^ 3) ^ q := Nat.pow_lt_pow_left hlarge hq_pos.ne'
        _ = n ^ (3 * q) := by rw [pow_mul]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 1 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      calc
        i ^ i = (i ^ 4) ^ q * i := by
          rw [hi_eq, pow_add, pow_mul, pow_one]
        _ ≤ (n ^ 3) ^ q * i := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n :=
          Nat.mul_lt_mul_of_pos_left hin
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 1) := by
          rw [← pow_mul, ← pow_succ]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 2 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      have hsquare_lt : i ^ 2 < n ^ 2 :=
        Nat.pow_lt_pow_left hin (by norm_num)
      calc
        i ^ i = (i ^ 4) ^ q * i ^ 2 := by
          rw [hi_eq, pow_add, pow_mul]
        _ ≤ (n ^ 3) ^ q * i ^ 2 := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hsquare_lt
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 2) := by
          rw [← pow_mul, ← pow_add]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 3 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      have hcube_lt : i ^ 3 < n ^ 3 :=
        Nat.pow_lt_pow_left hin (by norm_num)
      calc
        i ^ i = (i ^ 4) ^ q * i ^ 3 := by
          rw [hi_eq, pow_add, pow_mul]
        _ ≤ (n ^ 3) ^ q * i ^ 3 := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n ^ 3 :=
          Nat.mul_lt_mul_of_pos_left hcube_lt
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 3) := by
          rw [← pow_mul, ← pow_add]
        _ = n ^ (i - q) := by
          congr 1
          omega
  calc
    i ^ i * n ^ (i / 4) = i ^ i * n ^ q := by rfl
    _ < n ^ (i - q) * n ^ q :=
      Nat.mul_lt_mul_of_pos_right hi_pow_lt (Nat.pow_pos (a := n) (n := q) hn_pos)
    _ = n ^ (i - q + q) := by rw [← pow_add]
    _ = n ^ i := by
      congr 1
      dsimp [q]
      omega

