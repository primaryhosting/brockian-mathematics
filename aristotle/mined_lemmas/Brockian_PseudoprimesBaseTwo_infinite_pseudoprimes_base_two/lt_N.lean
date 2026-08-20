import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma lt_N {p : ℕ} (hp : 5 ≤ p) : p < N p := by
  have hb := one_lt_B hp
  have h2p : p + 2 ≤ 2 ^ p :=
    Nat.le_induction (by norm_num) (fun k _ ih => by rw [pow_succ]; omega) p hp
  have h1 : p < A p := by rw [A]; omega
  rw [N]
  nlinarith

