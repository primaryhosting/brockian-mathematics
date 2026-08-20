import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma three_mul_B (p : ℕ) (hp : Odd p) : 3 * B p = 2 ^ p + 1 := by
  have h : 3 ∣ 2 ^ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    obtain ⟨k, rfl⟩ := hp
    norm_num [Nat.add_mod, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  rw [B, Nat.mul_div_cancel' h]

