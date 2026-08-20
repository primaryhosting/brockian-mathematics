import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma N_not_prime {p : ℕ} (hp : 5 ≤ p) : ¬ (N p).Prime := by
  unfold N
  show ¬ (A p * B p).Prime
  by_contra h
  have hAp : 1 < A p := one_lt_A hp
  have hBp : 1 < B p := one_lt_B hp
  exact Nat.not_prime_mul (by omega : A p ≠ 1) (by omega : B p ≠ 1) h

