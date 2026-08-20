import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma one_lt_N {p : ℕ} (hp : 5 ≤ p) : 1 < N p := by
  have ha := one_lt_A hp
  have hb := one_lt_B hp
  rw [N]
  nlinarith

