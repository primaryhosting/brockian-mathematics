import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma three_mul_N (p : ℕ) (hp : Odd p) : 3 * N p + 1 = 4 ^ p := by
  rw [N, mul_comm (A p) (B p), ← mul_assoc, three_mul_B p hp, A]
  have key : (2 ^ p + 1) * (2 ^ p - 1) = 4 ^ p - 1 := by
    have h4 : (4 : ℕ) ^ p = 2 ^ p * 2 ^ p := by
      rw [← Nat.pow_add, ← two_mul, pow_mul]; norm_num
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ p = y + 1 :=
      ⟨2 ^ p - 1, by have := Nat.one_le_pow p 2 (by norm_num); omega⟩
    have hkey : (y + 1) * (y + 1) = (y + 1 + 1) * y + 1 := by ring
    rw [h4, hy, Nat.add_sub_cancel]
    omega
  rw [key]
  exact Nat.sub_add_cancel (Nat.one_le_pow p 4 (by norm_num))

