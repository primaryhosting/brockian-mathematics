import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma two_pow_two_mul_modEq {p : ℕ} (hp : Odd p) : 2 ^ (2 * p) ≡ 1 [MOD N p] := by
  have h : 2 ^ (2 * p) = 4 ^ p := by rw [pow_mul]; norm_num
  rw [h]
  exact four_pow_modEq hp

/-- The key congruence: `2 ^ (N p) ≡ 2 [MOD N p]`. -/
