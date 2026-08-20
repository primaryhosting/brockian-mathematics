import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma N_odd (p : ℕ) (hp : Odd p) : Odd (N p) := by
  rw [N, A, B]
  have hp1 : 1 ≤ p := hp.pos
  have h2p_even : Even (2 ^ p) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hAp_odd : Odd (2 ^ p - 1) := by
    rw [← Nat.not_even_iff_odd, Nat.even_sub (Nat.one_le_pow p 2 (by norm_num))]
    simp [h2p_even]
  have hBp_odd : Odd ((2 ^ p + 1) / 3) := by
    have h := three_mul_B p hp
    rw [B] at h
    have hodd2 : Odd (2 ^ p + 1) := by
      obtain ⟨k, hk⟩ := h2p_even
      exact ⟨k, by omega⟩
    obtain ⟨m, hm⟩ := hodd2
    rw [← h] at hm
    exact ⟨m / 3, by omega⟩
  exact hAp_odd.mul hBp_odd

/-- `p ∣ N p - 1`, coming from Fermat's little theorem `4 ^ p ≡ 4 [MOD p]`. -/
