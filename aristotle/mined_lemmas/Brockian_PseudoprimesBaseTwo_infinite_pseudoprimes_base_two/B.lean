import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private def B (p : ℕ) : ℕ := (2 ^ p + 1) / 3

/-- `N p = (4 ^ p - 1) / 3`, written as a product. -/
