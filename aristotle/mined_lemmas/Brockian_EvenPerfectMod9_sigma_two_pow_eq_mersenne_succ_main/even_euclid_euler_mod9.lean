import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/

theorem even_euclid_euler_mod9 {k : ℕ} (hk : Even k) :
    (2 ^ k * mersenne (k + 1)) % 9 = 1 := by
  have residue (q r : ℕ) (hr : r = 0 ∨ r = 2 ∨ r = 4) :
      (2 ^ (6 * q + r) * mersenne (6 * q + r + 1)) % 9 = 1 := by
    have hbase : Nat.ModEq 9 (2 ^ 6) 1 := by norm_num
    have hpow0 : Nat.ModEq 9 (2 ^ (6 * q)) 1 := by
      rw [pow_mul]
      simpa using hbase.pow q
    rcases hr with rfl | rfl | rfl
    · have hnext : Nat.ModEq 9 (2 ^ (6 * q + 0 + 1)) 2 := by
        rw [show 6 * q + 0 + 1 = 6 * q + 1 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 1) 2 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 0 + 1)) 1 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      simpa using hpow0.mul hm
    · have hpow : Nat.ModEq 9 (2 ^ (6 * q + 2)) 4 := by
        rw [pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 2) 4 by norm_num)
      have hnext : Nat.ModEq 9 (2 ^ (6 * q + 2 + 1)) 8 := by
        rw [show 6 * q + 2 + 1 = 6 * q + 3 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 3) 8 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 2 + 1)) 7 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      exact hpow.mul hm
    · have hpow : Nat.ModEq 9 (2 ^ (6 * q + 4)) 7 := by
        rw [pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 4) 7 by norm_num)
      have hnext : Nat.ModEq 9 (2 ^ (6 * q + 4 + 1)) 5 := by
        rw [show 6 * q + 4 + 1 = 6 * q + 5 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 5) 5 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 4 + 1)) 4 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      exact hpow.mul hm
  obtain ⟨t, rfl⟩ := hk
  have ht := Nat.mod_add_div t 3
  have hlt := Nat.mod_lt t (by norm_num : 0 < 3)
  interval_cases hrem : t % 3
  · have heq : t + t = 6 * (t / 3) + 0 := by omega
    rw [heq]
    exact residue (t / 3) 0 (Or.inl rfl)
  · have heq : t + t = 6 * (t / 3) + 2 := by omega
    rw [heq]
    exact residue (t / 3) 2 (Or.inr (Or.inl rfl))
  · have heq : t + t = 6 * (t / 3) + 4 := by omega
    rw [heq]
    exact residue (t / 3) 4 (Or.inr (Or.inr rfl))

/-- Every even perfect number greater than 6 is congruent to 1 modulo 9. -/
