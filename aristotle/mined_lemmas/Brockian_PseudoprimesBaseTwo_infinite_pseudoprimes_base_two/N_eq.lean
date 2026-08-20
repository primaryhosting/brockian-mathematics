import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma N_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ∃ k, N p = 2 * p * k + 1 := by
  obtain ⟨k, hk⟩ := two_p_dvd_N_sub_one hp h5
  have hN : 1 < N p := one_lt_N h5
  exact ⟨k, by omega⟩

/-- `4 ^ p ≡ 1 [MOD N p]`, since `4 ^ p = 3 * N p + 1`. -/
