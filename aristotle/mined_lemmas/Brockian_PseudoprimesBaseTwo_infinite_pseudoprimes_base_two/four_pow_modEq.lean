import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma four_pow_modEq {p : ℕ} (hp : Odd p) : 4 ^ p ≡ 1 [MOD N p] := by
  have h := three_mul_N p hp
  exact Nat.ModEq.symm (Nat.modEq_of_dvd ⟨3, by omega⟩)

/-- The order of `2` divides `2 * p` modulo `N p`. -/
