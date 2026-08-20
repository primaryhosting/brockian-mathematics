import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma one_lt_A {p : ℕ} (hp : 5 ≤ p) : 1 < A p := by
  show 1 < 2 ^ p - 1
  have : 2 ^ p ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hp
  omega

