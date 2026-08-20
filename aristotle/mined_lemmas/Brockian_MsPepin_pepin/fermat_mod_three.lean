import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma fermat_mod_three (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 3 = 2 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have h3 : 2 ^ (2 ^ n) = (2 ^ 2) ^ (2 ^ (n - 1)) := by rw [h2, pow_mul]
  rw [h3]
  norm_num at *
  have h4 : 4 ^ 2 ^ (n - 1) % 3 = 1 := by
    have := Nat.pow_mod 4 (2 ^ (n - 1)) 3
    simp [this]
  rw [Nat.add_mod, h4]

/-- `2` is not a square modulo `3`. -/
