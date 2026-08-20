import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma fermat_mod_four (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 4 = 1 := by
  have h : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have h2 : 4 ∣ 2 ^ (2 ^ n) := pow_dvd_pow 2 h
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd h2]

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `2` mod `3`. -/
