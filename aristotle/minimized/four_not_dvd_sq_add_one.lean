import Mathlib

theorem four_not_dvd_sq_add_one (n : ℕ) : ¬ (4 ∣ n ^ 2 + 1) := by
  intro h
  have hm : (n ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h
  have h2 : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hh : (n % 4) <;> omega
